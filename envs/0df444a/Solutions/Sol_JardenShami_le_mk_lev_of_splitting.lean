-- Prove2me | solution 1 for JardenShami.le_mk_lev_of_splitting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:00.677709+00:00
-- url     : https://prove2.me/submissions/90edbc85-44e0-4c52-8f92-269211708716

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
import Theorems.Thm_JardenShami_le_of_le_of_le_of_ht_le
import Theorems.Thm_JardenShami_Kappa_mk_eq
import Theorems.Thm_JardenShami_Tree_eq_of_le_of_le_of_ht_eq


set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution {T : Type w} [PartialOrder T] [IsTree T] {ρ : Cardinal.{w}}
    {α α₀ : Ordinal.{w}} (hext : ∀ x : T, ht x < α → ∃ y ∈ Lev T α, x < y)
    (hbd : ∀ (ι : Type w) (f : ι → Ordinal.{w}), #ι < ρ → (∀ i, f i < α) →
      ∃ q < α, ∀ i, f i ≤ q)
    (hα₀ : α₀ < α)
    (hsplit : ∀ q : Ordinal.{w}, α₀ ≤ q → q < α → ∃ a b c : T, ht a = q ∧ q < ht b ∧
      ht b < α ∧ ht c = ht b ∧ a < b ∧ a < c ∧ b ≠ c) :
    ρ ≤ #(Lev T α) := by
  classical
  obtain ⟨t₀, -⟩ := hsplit α₀ le_rfl hα₀
  have : Nonempty T := ⟨t₀⟩
  -- the splitting data `a_q, b_q, c_q` and the extensions `E x ∈ Lev_α(T)`
  have hs : ∀ q : Ordinal.{w}, ∃ a b c : T, α₀ ≤ q → q < α → ht a = q ∧ q < ht b ∧
      ht b < α ∧ ht c = ht b ∧ a < b ∧ a < c ∧ b ≠ c := by
    intro q
    by_cases h : α₀ ≤ q ∧ q < α
    · obtain ⟨a, b, c, hh⟩ := hsplit q h.1 h.2
      exact ⟨a, b, c, fun _ _ => hh⟩
    · exact ⟨t₀, t₀, t₀, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose sa sb sc hsabc using hs
  have he : ∀ x : T, ∃ y : T, ht x < α → y ∈ Lev T α ∧ x < y := by
    intro x
    by_cases h : ht x < α
    · obtain ⟨y, hy, hxy⟩ := hext x h
      exact ⟨y, fun _ => ⟨hy, hxy⟩⟩
    · exact ⟨x, fun h' => absurd h' h⟩
  choose E hE using he
  -- the recursion: `x i ∈ {b_q, c_q}` for `q = max α₀ (sup_{j<i} ht (x j))`
  obtain ⟨x, hx⟩ : ∃ x : Kappa ρ → T, ∀ i, x i =
      if ∃ j, ∃ _ : j < i, sb (max α₀ (⨆ j : Set.Iio i, ht (x j))) ≤ E (x j)
      then sc (max α₀ (⨆ j : Set.Iio i, ht (x j)))
      else sb (max α₀ (⨆ j : Set.Iio i, ht (x j))) :=
    ⟨wellFounded_lt.fix fun i ih =>
      if ∃ j, ∃ hj : j < i, sb (max α₀ (⨆ j : Set.Iio i, ht (ih j j.2))) ≤ E (ih j hj)
      then sc (max α₀ (⨆ j : Set.Iio i, ht (ih j j.2)))
      else sb (max α₀ (⨆ j : Set.Iio i, ht (ih j j.2))),
      fun i => by rw [WellFounded.fix_eq]⟩
  set Q : Kappa ρ → Ordinal.{w} := fun i => max α₀ (⨆ j : Set.Iio i, ht (x j)) with hQdef
  have hQle : ∀ i, ∀ j < i, ht (x j) ≤ Q i := fun i j hj =>
    (Ordinal.le_iSup (fun j : Set.Iio i => ht (x j)) ⟨j, hj⟩).trans (le_max_right _ _)
  -- heights stay below `α`
  have hmain : ∀ i, Q i < α ∧ ht (x i) < α := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i IH =>
    have hQ : Q i < α := by
      obtain ⟨q, hq, hqb⟩ := hbd (Set.Iio i) (fun j => ht (x j))
        (by
          have := Cardinal.mk_Iio_lt i (by rw [Kappa.mk_eq, Ordinal.type_toType])
          rwa [Kappa.mk_eq] at this)
        (fun j => (IH j j.2).2)
      exact max_lt hα₀ ((Ordinal.iSup_le hqb).trans_lt hq)
    refine ⟨hQ, ?_⟩
    obtain ⟨-, -, hb, hc, -⟩ := hsabc (Q i) (le_max_left _ _) hQ
    rw [hx i]
    split_ifs
    · rw [hc]; exact hb
    · exact hb
  have hdata : ∀ i, ht (sa (Q i)) = Q i ∧ Q i < ht (sb (Q i)) ∧ ht (sb (Q i)) < α ∧
      ht (sc (Q i)) = ht (sb (Q i)) ∧ sa (Q i) < sb (Q i) ∧ sa (Q i) < sc (Q i) ∧
        sb (Q i) ≠ sc (Q i) := fun i => hsabc (Q i) (le_max_left _ _) (hmain i).1
  let d : Kappa ρ → T := fun i => E (x i)
  have hd : ∀ i, d i ∈ Lev T α ∧ x i < d i := fun i => hE (x i) (hmain i).2
  -- the key property: `x i` is below no earlier `d j`
  have key : ∀ i, ∀ j < i, ¬ x i ≤ d j := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i IH =>
    intro j hj hle
    obtain ⟨ha, -, -, hcb, hab, hac, hbc⟩ := hdata i
    by_cases hcase : ∃ j, ∃ _ : j < i, sb (Q i) ≤ E (x j)
    · have hxi : x i = sc (Q i) := by
        rw [hx i]
        split_ifs with h
        · rfl
        · exact absurd hcase h
      obtain ⟨j₀, hj₀, hb₀⟩ := hcase
      rw [hxi] at hle
      by_cases hjj : j = j₀
      · subst hjj
        exact hbc (eq_of_le_of_le_of_ht_eq hb₀ hle hcb.symm)
      · -- `d j` and `d j₀` both lie above `a_q`
        have h1 : sa (Q i) ≤ d j := (hac.le.trans hle)
        have h2 : sa (Q i) ≤ d j₀ := hab.le.trans hb₀
        rcases lt_or_gt_of_ne hjj with hlt | hlt
        · -- `j < j₀`: `x j₀ ≤ a_q ≤ d j`
          have : x j₀ ≤ sa (Q i) := le_of_le_of_le_of_ht_le (hd j₀).2.le h2
            (by rw [ha]; exact hQle i j₀ hj₀)
          exact IH j₀ hj₀ j hlt (this.trans h1)
        · have : x j ≤ sa (Q i) := le_of_le_of_le_of_ht_le (hd j).2.le h1
            (by rw [ha]; exact hQle i j hj)
          exact IH j hj j₀ hlt (this.trans h2)
    · have hxi : x i = sb (Q i) := by
        rw [hx i]
        split_ifs with h
        · exact absurd h hcase
        · rfl
      rw [hxi] at hle
      exact hcase ⟨j, hj, hle⟩
  have hdinj : Function.Injective fun i : Kappa ρ => (⟨d i, (hd i).1⟩ : Lev T α) := by
    intro i j h
    have h' : d i = d j := congrArg (fun z : Lev T α => (z : T)) h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key j i hlt (h' ▸ (hd j).2.le)
    · exact key i j hlt (h' ▸ (hd i).2.le)
  have := Cardinal.mk_le_of_injective hdinj
  rwa [Kappa.mk_eq] at this
end JardenShami
