-- Prove2me | solution 1 for JechSetTheory.solovay_split
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T07:15:19.224313+00:00
-- url     : https://prove2.me/submissions/704d33b7-61ed-4901-996a-258253b80aa6

import Mathlib
import Definitions.Def_JechStationary

/-! cc679192 JechSetTheory.solovay_split (Solovay, Jech 8.10).

Library (namespace `JechLib`): `isClub_diag` + `fodor` (reused from 5e6cebaa),
`split_of_fibres` (a cofinal set of stationary fibres of one function splits `A`),
`case_short` (stationarily many points with a ladder of length `< α`: Fodor on the ladder
length, then a coordinate `ξ` whose values are stationarily unbounded) and `case_long`
(Jech 8.9 reflection: a stationary `W₀ ⊆ W` whose points carry clubs avoiding `W`,
then press down along those clubs).
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

section Solovay

variable {I : Type u} [LinearOrder I] [WellFoundedLT I]

omit [WellFoundedLT I] in
theorem nonempty_of_cof' (hI : ℵ₀ < cof I) : Nonempty I := nonempty_of_cof hI

theorem IsStationary.inter_club (hI : ℵ₀ < cof I) {T C : Set I} (hT : IsStationary T)
    (hC : IsClub C) : IsStationary (T ∩ C) := by
  intro D hD
  obtain ⟨b, hbT, hbC, hbD⟩ := hT (hC.inter hI.ne' hD)
  exact ⟨b, ⟨hbT, hbC⟩, hbD⟩

omit [WellFoundedLT I] in
/-- Assembly: a cofinal family of stationary fibres of `r` on `B ⊆ A` splits `A` into
`#I` disjoint stationary pieces. -/
theorem split_of_fibres (hI : ℵ₀ < cof I) (hmk : #I = cof I) {A B : Set I} (hBA : B ⊆ A)
    (r : I → I) (hΓ : ∀ η, ∃ β, η ≤ β ∧ IsStationary {α | α ∈ B ∧ r α = β}) :
    ∃ S : I → Set I, (∀ i, IsStationary (S i)) ∧ (Pairwise fun i j => Disjoint (S i) (S j)) ∧
      A = ⋃ i, S i := by
  classical
  let Γ : Set I := {β | IsStationary {α | α ∈ B ∧ r α = β}}
  have hΓc : IsCofinal Γ := fun η => by
    obtain ⟨β, hβ, hs⟩ := hΓ η
    exact ⟨β, hs, hβ⟩
  have hcard : #Γ = #I := le_antisymm (mk_set_le _) (hmk.le.trans (Order.cof_le hΓc))
  obtain ⟨e⟩ : Nonempty (I ≃ Γ) := Cardinal.eq.1 hcard.symm
  obtain ⟨i0⟩ := nonempty_of_cof hI
  let L : I → I := fun α => if h : r α ∈ Γ ∧ α ∈ B then e.symm ⟨r α, h.1⟩ else i0
  refine ⟨fun i => {α | α ∈ A ∧ L α = i}, fun i => ?_, fun i j hij => ?_, ?_⟩
  · have hs : IsStationary {α | α ∈ B ∧ r α = (e i).1} := (e i).2
    refine hs.mono fun α hα => ⟨hBA hα.1, ?_⟩
    have h : r α ∈ Γ ∧ α ∈ B := ⟨hα.2 ▸ (e i).2, hα.1⟩
    simp only [L, dif_pos h]
    rw [Equiv.symm_apply_eq]
    exact Subtype.ext hα.2
  · refine Set.disjoint_left.2 ?_
    rintro α ⟨-, hi⟩ ⟨-, hj⟩
    exact hij (hi.symm.trans hj)
  · ext α
    simp only [mem_iUnion, mem_setOf_eq]
    exact ⟨fun h => ⟨L α, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩

/-- Jech 8.10, the case of stationarily many points with a short ladder. -/
theorem case_short (hI : ℵ₀ < cof I) (hIio : ∀ x : I, #(Iio x) < cof I) {B : Set I}
    (hB : IsStationary B)
    (hlad : ∀ α ∈ B, ∃ c < α, ∃ g : I → I, (∀ x < c, g x < α) ∧ ∀ y < α, ∃ x < c, y ≤ g x) :
    ∃ B' ⊆ B, ∃ r : I → I, ∀ η, ∃ β, η ≤ β ∧ IsStationary {α | α ∈ B' ∧ r α = β} := by
  classical
  have := noMaxOrder_of_cof hI
  have h' : ∀ α, ∃ c : I, ∃ g : I → I, α ∈ B → c < α ∧ (∀ x < c, g x < α) ∧
      ∀ y < α, ∃ x < c, y ≤ g x := fun α => by
    by_cases hα : α ∈ B
    · obtain ⟨c, hc, g, hg⟩ := hlad α hα
      exact ⟨c, g, fun _ => ⟨hc, hg⟩⟩
    · exact ⟨α, id, fun h => absurd h hα⟩
  choose c g hcg using h'
  obtain ⟨c0, hc0⟩ := fodor hI hIio hB c (fun α hα => (hcg α hα).1)
  have hclaim : ∃ ξ < c0, ∀ η, IsStationary {α | (α ∈ B ∧ c α = c0) ∧ η ≤ g α ξ} := by
    by_contra hn
    push Not at hn
    have hC : ∀ ξ, ∃ η, ∃ C, IsClub C ∧
        (ξ < c0 → Disjoint {α | (α ∈ B ∧ c α = c0) ∧ η ≤ g α ξ} C) := fun ξ => by
      by_cases hξ : ξ < c0
      · obtain ⟨η, hη⟩ := hn ξ hξ
        obtain ⟨C, hC, hd⟩ := not_isStationary_iff.1 hη
        exact ⟨η, C, hC, fun _ => hd⟩
      · exact ⟨ξ, univ, IsClub.univ, fun h => absurd h hξ⟩
    choose η C hC hdisj using hC
    have hCc : IsClub (⋂ ξ : Iio c0, C ξ) :=
      IsClub.iInter hI.ne' (by simpa using hIio c0) (fun ξ => hC ξ)
    have hnc : ¬ IsCofinal (range fun ξ : Iio c0 => η ξ) := fun h =>
      (Order.cof_le h).not_gt (mk_range_le.trans_lt (hIio c0))
    obtain ⟨y, hy⟩ := not_isCofinal_iff.1 hnc
    obtain ⟨α, hαB, hαC, hαy⟩ := hc0 (hCc.inter hI.ne' (isClub_Ioi y))
    obtain ⟨-, -, hcof⟩ := hcg α hαB.1
    obtain ⟨x, hx, hyx⟩ := hcof y hαy
    rw [hαB.2] at hx
    exact Set.disjoint_left.1 (hdisj x hx) ⟨hαB, (hy _ ⟨⟨x, hx⟩, rfl⟩).le.trans hyx⟩
      (mem_iInter.1 hαC ⟨x, hx⟩)
  obtain ⟨ξ0, hξc, hξ0⟩ := hclaim
  refine ⟨{α | α ∈ B ∧ c α = c0}, fun α hα => hα.1, fun α => g α ξ0, fun η' => ?_⟩
  obtain ⟨β, hβ⟩ := fodor hI hIio (hξ0 η') (fun α => g α ξ0)
    (fun α hα => (hcg α hα.1.1).2.1 ξ0 (by rw [hα.1.2]; exact hξc))
  obtain ⟨α, ⟨-, hηα⟩, hαβ⟩ := hβ.nonempty
  exact ⟨β, hαβ ▸ hηα, hβ.mono fun x hx => ⟨hx.1.1, hx.2⟩⟩

/-- Jech 8.9 + 8.10, the case of stationarily many points of uncountable cofinality with no
short ladder: reflect to a stationary `W₀` whose points carry clubs avoiding `W`, then press
down along those clubs. -/
theorem case_long (hI : ℵ₀ < cof I) (hIio : ∀ x : I, #(Iio x) < cof I) {W : Set I}
    (hW : IsStationary W)
    (hP : ∀ α ∈ W, ¬ IsMin α ∧ ∀ s : ℕ → I, (∀ n, s n < α) → ∃ y < α, ∀ n, s n < y) :
    ∃ B' ⊆ W, ∃ r : I → I, ∀ η, ∃ β, η ≤ β ∧ IsStationary {α | α ∈ B' ∧ r α = β} := by
  classical
  have := noMaxOrder_of_cof hI
  let W0 : Set I := {α | α ∈ W ∧ ∃ D : Set I, Disjoint D W ∧
      (∀ ξ < α, ∃ d ∈ D, ξ < d ∧ d < α) ∧
      ∀ γ < α, ¬ IsMin γ → (∀ ξ < γ, ∃ d ∈ D, ξ < d ∧ d < γ) → γ ∈ D}
  have hW0 : IsStationary W0 := by
    intro C hC
    have hnext : ∀ ξ : I, ∃ d ∈ C, ξ < d := fun ξ => by
      obtain ⟨z, hz⟩ := exists_gt ξ
      obtain ⟨d, hd, hzd⟩ := hC.isCofinal z
      exact ⟨d, hd, hz.trans_le hzd⟩
    choose nx hnxC hnx using hnext
    obtain ⟨a⟩ := nonempty_of_cof hI
    have hD0 : IsClub ({γ | ∀ ξ < γ, γ ∈ Ioi (nx ξ)} ∩ Ioi a) :=
      (isClub_diag hI hIio (fun ξ => Ioi (nx ξ)) (fun ξ => isClub_Ioi _)).inter hI.ne'
        (isClub_Ioi a)
    let L : Set I := {γ | ¬ IsMin γ ∧ ∀ ξ < γ, ∃ d ∈ C, ξ < d ∧ d < γ}
    have hne : (W ∩ L).Nonempty := by
      obtain ⟨γ, hγW, hγD, hγa⟩ := hW hD0
      exact ⟨γ, hγW, fun hmin => hmin.not_lt hγa,
        fun ξ hξ => ⟨nx ξ, hnxC ξ, hnx ξ, hγD ξ hξ⟩⟩
    have hαWL : wellFounded_lt.min (W ∩ L) hne ∈ W ∩ L := WellFounded.min_mem _ _ hne
    have hαmin : ∀ x ∈ W ∩ L, ¬ x < wellFounded_lt.min (W ∩ L) hne := fun x hx =>
      WellFounded.not_lt_min _ _ hx
    set α := wellFounded_lt.min (W ∩ L) hne with hαdef
    have hLC : ∀ γ ∈ L, γ ∈ C := by
      rintro γ ⟨hγm, hγ⟩
      obtain ⟨ξ, hξ⟩ := not_isMin_iff.1 hγm
      obtain ⟨d, hdC, -, hdγ⟩ := hγ ξ hξ
      refine hC.isLUB_mem (t := C ∩ Iio γ) inter_subset_left ⟨d, hdC, hdγ⟩
        ⟨fun x hx => le_of_lt hx.2, fun b hb => ?_⟩
      by_contra hbγ
      push Not at hbγ
      obtain ⟨d', hd'C, hbd', hd'γ⟩ := hγ b hbγ
      exact absurd (hb ⟨hd'C, hd'γ⟩) (not_le.2 hbd')
    refine ⟨α, ⟨hαWL.1, L ∩ Iio α, ?_, ?_, ?_⟩, hLC α hαWL.2⟩
    · rw [Set.disjoint_left]
      rintro x ⟨hxL, hxα⟩ hxW
      exact hαmin x ⟨hxW, hxL⟩ hxα
    · intro ξ hξ
      have hstep : ∀ x : I, ∃ d, x < α → d ∈ C ∧ x < d ∧ d < α := fun x => by
        by_cases hx : x < α
        · obtain ⟨d, hd⟩ := hαWL.2.2 x hx
          exact ⟨d, fun _ => hd⟩
        · exact ⟨x, fun h => absurd h hx⟩
      choose st hst using hstep
      let s : ℕ → I := fun n => Nat.rec (st ξ) (fun _ x => st x) n
      have hsS : ∀ n, s (n + 1) = st (s n) := fun n => rfl
      have hslt : ∀ n, s n < α := by
        intro n
        induction n with
        | zero => exact (hst ξ hξ).2.2
        | succ n ih => rw [hsS]; exact (hst _ ih).2.2
      have hsC : ∀ n, s n ∈ C := by
        intro n
        cases n with
        | zero => exact (hst ξ hξ).1
        | succ n => rw [hsS]; exact (hst _ (hslt n)).1
      have hsinc : ∀ n, s n < s (n + 1) := fun n => by rw [hsS]; exact (hst _ (hslt n)).2.1
      have hξs : ξ < s 0 := (hst ξ hξ).2.1
      obtain ⟨y, hyα, hy⟩ := (hP α hαWL.1).2 s hslt
      have : Nonempty I := ⟨ξ⟩
      let := WellFoundedLT.toOrderBot (α := I)
      let := WellFoundedLT.conditionallyCompleteLinearOrderBot I
      have hbdd : BddAbove (range s) := ⟨y, by rintro _ ⟨n, rfl⟩; exact (hy n).le⟩
      have hγα : sSup (range s) < α :=
        (csSup_le (range_nonempty s) (by rintro _ ⟨n, rfl⟩; exact (hy n).le)).trans_lt hyα
      have hγL : sSup (range s) ∈ L := by
        refine ⟨fun hmin => ?_, fun ζ hζ => ?_⟩
        · exact absurd (hmin (le_csSup hbdd ⟨0, rfl⟩))
            (not_le.2 ((hsinc 0).trans_le (le_csSup hbdd ⟨1, rfl⟩)))
        · obtain ⟨_, ⟨n, rfl⟩, hn⟩ := exists_lt_of_lt_csSup (range_nonempty s) hζ
          exact ⟨s (n + 1), hsC (n + 1), hn.trans (hsinc n),
            (hsinc (n + 1)).trans_le (le_csSup hbdd ⟨n + 2, rfl⟩)⟩
      exact ⟨sSup (range s), ⟨hγL, hγα⟩, hξs.trans_le (le_csSup hbdd ⟨0, rfl⟩), hγα⟩
    · intro γ hγα hγm hγ
      refine ⟨⟨hγm, fun ζ hζ => ?_⟩, hγα⟩
      obtain ⟨d, ⟨hdL, -⟩, hζd, hdγ⟩ := hγ ζ hζ
      obtain ⟨d', hd'C, hζd', hd'd⟩ := hdL.2 ζ hζd
      exact ⟨d', hd'C, hζd', hd'd.trans hdγ⟩
  have hD : ∀ α, ∃ D : Set I, α ∈ W0 → (Disjoint D W ∧ (∀ ξ < α, ∃ d ∈ D, ξ < d ∧ d < α) ∧
      ∀ γ < α, ¬ IsMin γ → (∀ ξ < γ, ∃ d ∈ D, ξ < d ∧ d < γ) → γ ∈ D) := fun α => by
    by_cases hα : α ∈ W0
    · obtain ⟨-, D, hD⟩ := hα
      exact ⟨D, fun _ => hD⟩
    · exact ⟨∅, fun h => absurd h hα⟩
  choose D hD using hD
  have ha : ∀ α ξ, ∃ d, α ∈ W0 → ξ < α → d ∈ D α ∧ ξ < d ∧ d < α := fun α ξ => by
    by_cases h : α ∈ W0 ∧ ξ < α
    · obtain ⟨d, hd⟩ := (hD α h.1).2.1 ξ h.2
      exact ⟨d, fun _ _ => hd⟩
    · exact ⟨α, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose a ha using ha
  have hclaim : ∃ ξ, ∀ η, IsStationary {α | α ∈ W0 ∧ ξ < α ∧ η ≤ a α ξ} := by
    by_contra hn
    push Not at hn
    choose η hη using hn
    have hC : ∀ ξ, ∃ C, IsClub C ∧ Disjoint {α | α ∈ W0 ∧ ξ < α ∧ η ξ ≤ a α ξ} C :=
      fun ξ => not_isStationary_iff.1 (hη ξ)
    choose C hC hdisj using hC
    have hCd : IsClub {γ | ∀ ξ < γ, γ ∈ C ξ ∩ Ioi (η ξ)} :=
      isClub_diag hI hIio _ fun ξ => (hC ξ).inter hI.ne' (isClub_Ioi _)
    obtain ⟨α1, hα1W, hα1C⟩ := hW0 hCd
    obtain ⟨α2, hα2W, hα2C, hα12⟩ := hW0 (hCd.inter hI.ne' (isClub_Ioi α1))
    have hmem : α1 ∈ D α2 := by
      refine (hD α2 hα2W).2.2 α1 hα12 (hP α1 hα1W.1).1 fun ξ hξ => ?_
      have hξ2 : ξ < α2 := hξ.trans hα12
      obtain ⟨hd, hξd, -⟩ := ha α2 ξ hα2W hξ2
      refine ⟨a α2 ξ, hd, hξd, ?_⟩
      have h1 : ¬ η ξ ≤ a α2 ξ := fun h =>
        Set.disjoint_left.1 (hdisj ξ) ⟨hα2W, hξ2, h⟩ (hα2C ξ hξ2).1
      exact (not_le.1 h1).trans (hα1C ξ hξ).2
    exact Set.disjoint_left.1 (hD α2 hα2W).1 hmem hα1W.1
  obtain ⟨ξ0, hξ0⟩ := hclaim
  refine ⟨W0, fun α hα => hα.1, fun α => a α ξ0, fun η' => ?_⟩
  obtain ⟨β, hβ⟩ := fodor hI hIio (hξ0 η') (fun α => a α ξ0)
    (fun α hα => (ha α ξ0 hα.1 hα.2.1).2.2)
  obtain ⟨α, ⟨-, -, hηα⟩, hαβ⟩ := hβ.nonempty
  exact ⟨β, hαβ ▸ hηα, hβ.mono fun x hx => ⟨hx.1.1, hx.2⟩⟩

end Solovay

end JechLib

open JechLib

set_option maxHeartbeats 4000000 in
open Cardinal Order Set JechSetTheory in
theorem solution (k : Cardinal) (hk : k.IsRegular) (hk₀ : ℵ₀ < k)
    (A : Set (Below k)) (hA : IsStationary A) :
    ∃ S : Below k → Set (Below k),
      (∀ i, IsStationary (S i)) ∧
      (Pairwise fun i j => Disjoint (S i) (S j)) ∧
      A = ⋃ i, S i := by
  classical
  have hcI : Order.cof (k.ord.ToType) = k := by
    rw [Ordinal.cof_toType, hk.cof_eq]
  have hmkI : #(k.ord.ToType) = k := by rw [mk_toType, card_ord]
  have hI : ℵ₀ < Order.cof (k.ord.ToType) := by rw [hcI]; exact hk₀
  have hIio : ∀ x : k.ord.ToType, #(Iio x) < Order.cof (k.ord.ToType) := fun x => by
    rw [hcI]; exact mk_Iio_toType_ord_lt x
  have := noMaxOrder_of_cof hI
  have hω : Ordinal.omega0 < k.ord := by rw [lt_ord, Ordinal.card_omega0]; exact hk₀
  have hn : ∀ n : ℕ, (n : Ordinal) < k.ord := fun n => (Ordinal.nat_lt_omega0 n).trans hω
  let w0 : k.ord.ToType := Ordinal.ToType.mk ⟨Ordinal.omega0, hω⟩
  let j : ℕ → k.ord.ToType := fun n => Ordinal.ToType.mk ⟨(n : Ordinal), hn n⟩
  have hj : Function.Injective j := fun m n h => by
    have h1 := Ordinal.ToType.mk.injective h
    exact Nat.cast_injective (congrArg Subtype.val h1)
  have hjw : ∀ n, j n < w0 := fun n => by
    show Ordinal.ToType.mk _ < Ordinal.ToType.mk _
    rw [OrderIso.lt_iff_lt]
    show (n : Ordinal) < Ordinal.omega0
    exact Ordinal.nat_lt_omega0 n
  let A1 : Set k.ord.ToType := A ∩ Ioi w0
  have hA1 : IsStationary A1 := IsStationary.inter_club hI hA (isClub_Ioi w0)
  let B : Set k.ord.ToType := {α | α ∈ A1 ∧ ∃ c < α, ∃ g : k.ord.ToType → k.ord.ToType,
    (∀ x < c, g x < α) ∧ ∀ y < α, ∃ x < c, y ≤ g x}
  let W : Set k.ord.ToType := {α | α ∈ A1 ∧ α ∉ B}
  have hunion : A1 = B ∪ W := Set.ext fun α =>
    ⟨fun h => (em (α ∈ B)).elim Or.inl (fun hB => Or.inr ⟨h, hB⟩),
      fun h => h.elim (fun h => h.1) (fun h => h.1)⟩
  have hBW : IsStationary (B ∪ W) := by rw [← hunion]; exact hA1
  have hmk : #(k.ord.ToType) = Order.cof (k.ord.ToType) := hmkI.trans hcI.symm
  rcases (isStationary_union_iff hI.ne').1 hBW with hB | hW
  · obtain ⟨B', hB'B, r, hr⟩ := case_short hI hIio hB (fun α hα => hα.2)
    exact split_of_fibres hI hmk (fun α hα => (hB'B hα).1.1) r hr
  · have hP : ∀ α ∈ W, ¬ IsMin α ∧ ∀ s : ℕ → k.ord.ToType, (∀ n, s n < α) →
        ∃ y < α, ∀ n, s n < y := by
      rintro α ⟨⟨hαA, hαw⟩, hαB⟩
      refine ⟨fun hmin => hmin.not_lt hαw, fun s hs => ?_⟩
      by_contra hno
      push Not at hno
      apply hαB
      refine ⟨⟨hαA, hαw⟩, w0, hαw, fun x => s (Function.invFun j x), fun x _ => hs _,
        fun y hy => ?_⟩
      obtain ⟨n, hn'⟩ := hno y hy
      refine ⟨j n, hjw n, ?_⟩
      show y ≤ s (Function.invFun j (j n))
      rw [Function.leftInverse_invFun hj n]
      exact hn'
    obtain ⟨B', hB'W, r, hr⟩ := case_long hI hIio hW hP
    exact split_of_fibres hI hmk (fun α hα => (hB'W hα).1.1) r hr
