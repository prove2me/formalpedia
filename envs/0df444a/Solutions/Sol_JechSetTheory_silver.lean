-- Prove2me | solution 1 for JechSetTheory.silver
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T18:51:18.33414+00:00
-- url     : https://prove2.me/submissions/cb678209-3e89-4895-babb-49ff073f4918

import Mathlib
import Definitions.Def_JechStationary

/-! 5e6cebaa JechSetTheory.silver (Silver's theorem, Jech 8.12), Baumgartner-Prikry route.

Let `λ = cf k > ω`, `I = λ.ord.ToType` (regular uncountable index), `J = k.ord.ToType`.
* `isClub_diag`: the diagonal intersection of `I`-many clubs is club; `fodor` follows.
* `lemmaA` (Jech 8.15): an almost-disjoint family of functions that are regressive into
  `D α = {x | ∃ β < α, x < E β}` on a stationary set has size `≤ k` (Fodor + counting).
* `lemmaB` (Jech 8.16): an almost-disjoint family `Φ i α ∈ W α` whose initial segments inject
  into `D α` has size `≤ k⁺` (the `F_g` dichotomy argument).
* `solution`: code `X ⊆ J` by `α ↦ (X ∩ D α) ∈ 𝒫(D α) ↪ (#D α)⁺`, using GCH below `k`.
-/

set_option autoImplicit false

universe u

open Cardinal Order Set

namespace SilverLib

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

/-- Jech 8.16 in coded form: an almost-disjoint family of functions `Φ i α ∈ W α`, where every
initial segment of `W α` injects into `D α`, has at most `k⁺` members. -/
theorem lemmaB (hI : ℵ₀ < cof I) (hIio : ∀ x : I, #(Iio x) < cof I) {k : Cardinal.{u}}
    (hk : ℵ₀ ≤ k) (hIk : #I ≤ k) (hpow : ∀ ν < k, ν ^ #I < k) (E : I → J)
    (hE : ∀ β, #(Iio (E β)) < k) (W : I → Type u) [∀ α, LinearOrder (W α)]
    (hW : ∀ α β, β < α → ∀ w : W α, #(Iic w) ≤ #{x : J | ∃ β < α, x < E β})
    {ι : Type u} (Φ : ι → ∀ α, W α)
    (had : ∀ i j, i ≠ j → ¬ IsCofinal {α | Φ i α = Φ j α}) : #ι ≤ succ k := by
  classical
  have hne : Nonempty I := nonempty_of_cof hI
  obtain ⟨a0⟩ := nonempty_of_cof hI
  have h2I : #(Set I) * k ≤ k := by
    rw [mk_set]
    calc 2 ^ #I * k ≤ k * k := by
          gcongr; exact (hpow 2 ((natCast_lt_aleph0 (n := 2)).trans_le hk)).le
      _ = k := mul_eq_self hk
  have hF : ∀ g : ι, #{i | IsStationary {α | Φ i α ≤ Φ g α}} ≤ k := by
    intro g
    have hT : ∀ T : {T : Set I // IsStationary T}, #{i | ∀ α ∈ T.1, Φ i α ≤ Φ g α} ≤ k := by
      rintro ⟨T, hT⟩
      have hemb : ∀ α, ∃ e : W α → J, a0 < α →
          (Set.InjOn e (Iic (Φ g α)) ∧ ∀ w ∈ Iic (Φ g α), ∃ β < α, e w < E β) := by
        intro α
        by_cases hα : a0 < α
        · obtain ⟨emb⟩ := (Cardinal.le_def _ _).1 (hW α a0 hα (Φ g α))
          refine ⟨fun w => if h : w ∈ Iic (Φ g α) then (emb ⟨w, h⟩).1 else E a0,
            fun _ => ⟨?_, ?_⟩⟩
          · intro w hw w' hw' hww'
            simp only [dif_pos hw, dif_pos hw'] at hww'
            exact congrArg Subtype.val (emb.injective (Subtype.ext hww'))
          · intro w hw
            simp only [dif_pos hw]
            exact (emb ⟨w, hw⟩).2
        · exact ⟨fun _ => E a0, fun h => absurd h hα⟩
      choose e he using hemb
      refine lemmaA hI hIio hk hIk hpow E hE (T ∩ Ioi a0) (IsStationary.inter_Ioi hI hT a0)
        (fun (i : {i | ∀ α ∈ T, Φ i α ≤ Φ g α}) α => e α (Φ i.1 α)) ?_ ?_
      · rintro ⟨i, hi⟩ α ⟨hαT, hα⟩
        exact (he α hα).2 _ (hi α hαT)
      · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij hcof
        apply had i j (fun h => hij (Subtype.ext h))
        refine hcof.mono ?_
        rintro α ⟨⟨hαT, hα⟩, heq⟩
        exact (he α hα).1 (hi α hαT) (hj α hαT) heq
    calc #{i | IsStationary {α | Φ i α ≤ Φ g α}}
        ≤ #(⋃ T : {T : Set I // IsStationary T}, {i | ∀ α ∈ T.1, Φ i α ≤ Φ g α}) :=
          mk_le_mk_of_subset fun i hi => mem_iUnion.2 ⟨⟨_, hi⟩, fun α hα => hα⟩
      _ ≤ sum fun T : {T : Set I // IsStationary T} => #{i | ∀ α ∈ T.1, Φ i α ≤ Φ g α} :=
          mk_iUnion_le_sum_mk
      _ ≤ sum fun _ : {T : Set I // IsStationary T} => k := sum_le_sum _ _ hT
      _ = #{T : Set I // IsStationary T} * k := sum_const' _ _
      _ ≤ #(Set I) * k := by gcongr; exact mk_subtype_le _
      _ ≤ k := h2I
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨G, -, hG⟩ := le_mk_iff_exists_subset.1
    (show succ k ≤ #(univ : Set ι) by rw [mk_univ]; exact hlt.le)
  have hU : #(⋃ g : G, {i | IsStationary {α | Φ i α ≤ Φ g.1 α}}) < #ι := by
    calc _ ≤ sum fun g : G => #{i | IsStationary {α | Φ i α ≤ Φ g.1 α}} := mk_iUnion_le_sum_mk
      _ ≤ sum fun _ : G => k := sum_le_sum _ _ fun g => hF g.1
      _ = #G * k := sum_const' _ _
      _ = succ k := by
          rw [hG]
          exact mul_eq_left (hk.trans (le_succ k)) (le_succ k)
            (ne_of_gt (aleph0_pos.trans_le hk))
      _ < #ι := hlt
  obtain ⟨f, hf⟩ : ∃ f, f ∉ ⋃ g : G, {i | IsStationary {α | Φ i α ≤ Φ g.1 α}} := by
    by_contra h
    push Not at h
    exact hU.not_ge (by rw [← mk_univ]; exact mk_le_mk_of_subset fun x _ => h x)
  have hGF : G ⊆ {i | IsStationary {α | Φ i α ≤ Φ f α}} := fun g hg => by
    have hnot : ¬ IsStationary {α | Φ f α ≤ Φ g α} := fun h => hf (mem_iUnion.2 ⟨⟨g, hg⟩, h⟩)
    obtain ⟨C, hC, hdisj⟩ := not_isStationary_iff.1 hnot
    refine (hC.isStationary hI.ne').mono fun α hα => ?_
    exact le_of_lt (not_le.1 fun h => Set.disjoint_left.1 hdisj h hα)
  have := (mk_le_mk_of_subset hGF).trans (hF f)
  rw [hG] at this
  exact (lt_succ k).not_ge this

end LemmaB

end SilverLib


set_option maxHeartbeats 4000000 in
open Cardinal Order Set JechSetTheory in
theorem solution (k : Cardinal) (hk : k.IsSingular) (hcf : ℵ₀ < k.ord.cof)
    (hgch : ∀ l : Cardinal, ℵ₀ ≤ l → l < k → 2 ^ l = Order.succ l) :
    2 ^ k = Order.succ k := by
  classical
  have hk0 : ℵ₀ ≤ k := hk.aleph0_le
  have hck : k.ord.cof < k := hk.cof_ord_lt
  have hk1 : ℵ₀ < k := hcf.trans hck
  have hlim : IsSuccLimit k := hk.isSuccLimit
  have hcI : Order.cof (k.ord.cof.ord.ToType) = k.ord.cof := by
    rw [Ordinal.cof_toType, Ordinal.cof_ord_cof]
  have hmkI : #(k.ord.cof.ord.ToType) = k.ord.cof := by rw [mk_toType, card_ord]
  have hI : ℵ₀ < Order.cof (k.ord.cof.ord.ToType) := by rw [hcI]; exact hcf
  have hIio : ∀ x : k.ord.cof.ord.ToType, #(Iio x) < Order.cof (k.ord.cof.ord.ToType) :=
    fun x => by rw [hcI]; exact mk_Iio_toType_ord_lt x
  have hcJ : Order.cof (k.ord.ToType) = k.ord.cof := Ordinal.cof_toType _
  have hIk : #(k.ord.cof.ord.ToType) ≤ k := by rw [hmkI]; exact hck.le
  have hpow : ∀ ν < k, ν ^ #(k.ord.cof.ord.ToType) < k := by
    intro ν hν
    rw [hmkI]
    have hμk : max (max ν k.ord.cof) ℵ₀ < k := max_lt (max_lt hν hck) hk1
    have hμ0 : ℵ₀ ≤ max (max ν k.ord.cof) ℵ₀ := le_max_right _ _
    calc ν ^ k.ord.cof ≤ (max (max ν k.ord.cof) ℵ₀) ^ k.ord.cof :=
          power_le_power_right ((le_max_left _ _).trans (le_max_left _ _))
      _ ≤ (max (max ν k.ord.cof) ℵ₀) ^ (max (max ν k.ord.cof) ℵ₀) :=
          power_le_power_left (ne_of_gt (aleph0_pos.trans_le hμ0))
            ((le_max_right _ _).trans (le_max_left _ _))
      _ = 2 ^ (max (max ν k.ord.cof) ℵ₀) := power_self_eq hμ0
      _ = succ (max (max ν k.ord.cof) ℵ₀) := hgch _ hμ0 hμk
      _ < k := hlim.succ_lt hμk
  have hJmax : NoMaxOrder (k.ord.ToType) := SilverLib.noMaxOrder_of_cof (by rw [hcJ]; exact hcf)
  have hImax : NoMaxOrder (k.ord.cof.ord.ToType) := SilverLib.noMaxOrder_of_cof hI
  obtain ⟨s, hs, hsc⟩ := Order.exists_cof_eq (k.ord.ToType)
  obtain ⟨e⟩ : Nonempty (k.ord.cof.ord.ToType ≃ s) := Cardinal.eq.1 (by rw [hmkI, hsc, hcJ])
  have hω : Ordinal.omega0 < k.ord := by rw [lt_ord, Ordinal.card_omega0]; exact hk1
  have hn : ∀ n : ℕ, (n : Ordinal) < k.ord := fun n => (Ordinal.nat_lt_omega0 n).trans hω
  let w0 : k.ord.ToType := Ordinal.ToType.mk ⟨Ordinal.omega0, hω⟩
  have hw0 : ℵ₀ ≤ #(Iio w0) := by
    let f : ℕ → Iio w0 := fun n => ⟨Ordinal.ToType.mk ⟨(n : Ordinal), hn n⟩, by
      show Ordinal.ToType.mk _ < Ordinal.ToType.mk _
      rw [OrderIso.lt_iff_lt]
      show (n : Ordinal) < Ordinal.omega0
      exact Ordinal.nat_lt_omega0 n⟩
    have hf : Function.Injective f := fun m n h => by
      have h1 := Ordinal.ToType.mk.injective (congrArg Subtype.val h)
      exact Nat.cast_injective (congrArg Subtype.val h1)
    exact Cardinal.infinite_iff.1 (Infinite.of_injective f hf)
  let E : k.ord.cof.ord.ToType → k.ord.ToType := fun β => max (e β).1 w0
  have hEcof : ∀ x : k.ord.ToType, ∃ β, x < E β := fun x => by
    obtain ⟨x', hx'⟩ := exists_gt x
    obtain ⟨y, hy, hxy⟩ := hs x'
    exact ⟨e.symm ⟨y, hy⟩, hx'.trans_le (by simp [E, hxy])⟩
  have hE : ∀ β, #(Iio (E β)) < k := fun β => mk_Iio_toType_ord_lt _
  have hDk : ∀ α, #{x : k.ord.ToType | ∃ β < α, x < E β} < k := by
    intro α
    have hnc : ¬ IsCofinal (E '' Iio α) := fun h => (Order.cof_le h).not_gt
      ((mk_image_le.trans_lt (hIio α)).trans_eq (hcI.trans hcJ.symm))
    obtain ⟨y, hy⟩ := not_isCofinal_iff.1 hnc
    refine (mk_le_mk_of_subset (fun x hx => ?_)).trans_lt (mk_Iio_toType_ord_lt y)
    obtain ⟨β, hβ, hx⟩ := hx
    exact hx.trans (hy _ ⟨β, hβ, rfl⟩)
  let ν : k.ord.cof.ord.ToType → Cardinal :=
    fun α => max #{x : k.ord.ToType | ∃ β < α, x < E β} ℵ₀
  have hW : ∀ α β, β < α → ∀ w : (succ (ν α)).ord.ToType,
      #(Iic w) ≤ #{x : k.ord.ToType | ∃ β < α, x < E β} := by
    intro α β hβ w
    have hinf : ℵ₀ ≤ #{x : k.ord.ToType | ∃ β < α, x < E β} :=
      hw0.trans (mk_le_mk_of_subset fun x hx => ⟨β, hβ, lt_of_lt_of_le hx (le_max_right _ _)⟩)
    have h2 : #(Iio w) ≤ ν α := le_of_lt_succ (mk_Iio_toType_ord_lt w)
    rw [← Iio_insert]
    calc #(insert w (Iio w) : Set _) ≤ #(Iio w) + 1 := mk_insert_le
      _ ≤ ν α + 1 := by gcongr
      _ = ν α := add_one_eq (le_max_right _ _)
      _ = _ := max_eq_left hinf
  have hemb : ∀ α, Nonempty (Set {x : k.ord.ToType | ∃ β < α, x < E β} ↪
      (succ (ν α)).ord.ToType) := fun α => by
    rw [← Cardinal.le_def, mk_set, mk_toType, card_ord,
      ← hgch (ν α) (le_max_right _ _) (max_lt (hDk α) hk1)]
    exact power_le_power_left two_ne_zero (le_max_left _ _)
  let emb : ∀ α, Set {x : k.ord.ToType | ∃ β < α, x < E β} ↪ (succ (ν α)).ord.ToType :=
    fun α => (hemb α).some
  let Φ : Set k.ord.ToType → ∀ α, (succ (ν α)).ord.ToType := fun X α => emb α {x | x.1 ∈ X}
  have had : ∀ X Y : Set k.ord.ToType, X ≠ Y → ¬ IsCofinal {α | Φ X α = Φ Y α} := by
    intro X Y hXY hcof
    obtain ⟨x, hx⟩ : ∃ x, ¬ (x ∈ X ↔ x ∈ Y) := by
      by_contra h
      push Not at h
      exact hXY (Set.ext h)
    obtain ⟨β, hβ⟩ := hEcof x
    obtain ⟨γ, hγ⟩ := exists_gt β
    obtain ⟨α, hα, hγα⟩ := hcof γ
    have h1 := (emb α).injective hα
    have h2 := congrArg (fun S : Set {x : k.ord.ToType | ∃ β < α, x < E β} =>
      (⟨x, β, hγ.trans_le hγα, hβ⟩ : {x : k.ord.ToType | ∃ β < α, x < E β}) ∈ S) h1
    exact hx (Iff.of_eq h2)
  have hmain := SilverLib.lemmaB hI hIio hk0 hIk hpow E hE (fun α => (succ (ν α)).ord.ToType)
    hW Φ had
  rw [mk_set, mk_toType, card_ord] at hmain
  exact le_antisymm hmain (Order.succ_le_of_lt (cantor k))
