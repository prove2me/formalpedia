-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.Glue.lem_5_1_proof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:02.963949+00:00
-- url     : https://prove2.me/submissions/2dadcc10-26de-46e7-88bc-1f7f854ed2e6

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
public import Definitions.Def_LeanPool_SteinerSpanners_Glue

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Glue
namespace HighDimSteinerSpanners.Proofs.Glue
theorem _root_.solution :
    ∀ (α β : ℤ), 1 ≤ α → α ≤ β →
      ∀ (L R : ℤ → ℤ),
        (∀ s : ℤ, α ≤ s → s ≤ β →
          α - 1 ≤ L s ∧ L s ≤ s - 1 ∧ s ≤ R s ∧ R s ≤ β ∧ (L s, R s) ≠ (α - 1, β)) →
        ∃ s t : ℤ,
          α ≤ s ∧ s < t ∧ t ≤ β ∧
          L s < L t ∧ L t ≤ s ∧ t ≤ R s + 1 ∧ R s + 1 ≤ R t := by
  have key : ∀ (n : ℕ) (α β : ℤ), β - α = n → 1 ≤ α → α ≤ β →
      ∀ (L R : ℤ → ℤ),
        (∀ s : ℤ, α ≤ s → s ≤ β →
          α - 1 ≤ L s ∧ L s ≤ s - 1 ∧ s ≤ R s ∧ R s ≤ β ∧ (L s, R s) ≠ (α - 1, β)) →
        ∃ s t : ℤ,
          α ≤ s ∧ s < t ∧ t ≤ β ∧
          L s < L t ∧ L t ≤ s ∧ t ≤ R s + 1 ∧ R s + 1 ≤ R t := by
    intro n
    induction n using Nat.strong_induction_on
    rename_i n ih
    intro α β hdiff hα hαβ L R hLR
    by_cases heq : α = β
    · subst heq
      obtain ⟨h1, h2, h3, h4, hne⟩ := hLR α le_rfl le_rfl
      exfalso; apply hne
      ext <;> omega
    · have hlt : α < β := lt_of_le_of_ne hαβ heq
      let S := (Finset.Icc α β).filter (fun s => L s = α - 1)
      have hα_mem : α ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_Icc]
        obtain ⟨h1, h2, _⟩ := hLR α le_rfl hαβ
        exact ⟨⟨le_rfl, hαβ⟩, by omega⟩
      let u := S.max' ⟨α, hα_mem⟩
      have hu_mem : u ∈ S := Finset.max'_mem S ⟨α, hα_mem⟩
      simp only [S, Finset.mem_filter, Finset.mem_Icc] at hu_mem
      obtain ⟨⟨hαu, huβ⟩, hLu⟩ := hu_mem
      obtain ⟨_, _, huRu, hRuβ, hune⟩ := hLR u hαu huβ
      have hRu_lt : R u < β := by
        by_contra! hge
        have hRu_eq : R u = β := by omega
        exact hune (Prod.ext hLu hRu_eq)
      have hLw_gt : ∀ w : ℤ, u + 1 ≤ w → w ≤ R u + 1 → α ≤ L w := by
        intro w hwu hwR
        obtain ⟨h1, _⟩ := hLR w (by omega) (by omega)
        by_contra! hlt_α
        have hLw_eq : L w = α - 1 := by omega
        have hw_mem : w ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, hLw_eq⟩
        have hw_le_u : w ≤ u := Finset.le_max' S w hw_mem
        omega
      by_cases hcase1 : ∃ v ∈ Finset.Icc (u + 1) (R u + 1), L v ≤ u ∧ R u + 1 ≤ R v
      · obtain ⟨v, hv_mem, hLvu, hRuv⟩ := hcase1
        rw [Finset.mem_Icc] at hv_mem
        have hLv_ge := hLw_gt v hv_mem.1 hv_mem.2
        exact ⟨u, v, hαu, by omega, by omega, by omega, hLvu, hv_mem.2, hRuv⟩
      · push Not at hcase1
        let α' := u + 1
        let β' := R u + 1
        let L' (w : ℤ) := max (L w) u
        let R' (w : ℤ) := min (R w) (R u + 1)
        have hm_lt : (β' - α').toNat < n := by
          dsimp [α', β']
          omega
        obtain ⟨s, t, hα's, hst, htβ', hL'st, hL'ts, htR's, hR'st⟩ :=
          ih (β' - α').toNat hm_lt α' β' (by dsimp [α', β']; omega) (by dsimp [α']; omega)
            (by dsimp [α', β']; omega) L' R' (by
              intro w hα'w hwβ'
              dsimp [α', β'] at hα'w hwβ'
              obtain ⟨_, hLw_ub, hwRw, _, _⟩ := hLR w (by omega) (by omega)
              refine ⟨by dsimp [L', α']; omega, by dsimp [L']; omega,
                by dsimp [R']; omega, by dsimp [R', β']; omega, ?_⟩
              intro heq_pair
              have h1 : max (L w) u = u + 1 - 1 := congr_arg Prod.fst heq_pair
              have h2 : min (R w) (R u + 1) = R u + 1 := congr_arg Prod.snd heq_pair
              have hLwu : L w ≤ u := by omega
              have hlt_R : R w < R u + 1 := hcase1 w (Finset.mem_Icc.mpr ⟨hα'w, hwβ'⟩) hLwu
              omega)
        dsimp [α', β', L', R'] at hα's htβ' hL'st hL'ts htR's hR'st
        exact ⟨s, t, by omega, hst, by omega, by omega, by omega, by omega, by omega⟩
  intro α β hα hαβ L R hLR
  exact key (β - α).toNat α β (by omega) hα hαβ L R hLR
end HighDimSteinerSpanners.Proofs.Glue
