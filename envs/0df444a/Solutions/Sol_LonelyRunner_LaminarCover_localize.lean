-- Prove2me | solution 1 for LonelyRunner.LaminarCover.localize
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T18:54:28.203324+00:00
-- url     : https://prove2.me/submissions/3cd4c44e-c519-4a00-8866-467089a5c5d2

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs

namespace LonelyRunner















































end LonelyRunner

namespace LonelyRunner.BadCover





















end LonelyRunner.BadCover

namespace LonelyRunner.LaminarCover

open Set

theorem exists_maximal_container {ι X : Type*} (T : Finset ι) (F : ι → Set X)
    {i : ι} (hi : i ∈ T) :
    ∃ j ∈ T, F i ⊆ F j ∧ ∀ k ∈ T, F j ⊆ F k → F k ⊆ F j := by
  classical
  obtain ⟨G, hiG, hG, hmax⟩ := (T.image F).exists_le_maximal
    (Finset.mem_image_of_mem F hi)
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hG
  exact ⟨j, hj, hiG, fun k hk h => hmax (Finset.mem_image_of_mem F hk) h⟩



end LonelyRunner.LaminarCover

namespace LonelyRunner.Farey



















end LonelyRunner.Farey

namespace LonelyRunner.CoprimeReplacements

open Farey BadCover





























end LonelyRunner.CoprimeReplacements

namespace LonelyRunner.SingleDeletion

open BadCover









end LonelyRunner.SingleDeletion

namespace LonelyRunner.BadCover











end LonelyRunner.BadCover

namespace LonelyRunner.MatchingArithmetic





end LonelyRunner.MatchingArithmetic

namespace LonelyRunner.LargeDeletionMatching

open BadCover SingleDeletion



















end LonelyRunner.LargeDeletionMatching

namespace LonelyRunner.SeparatedBands

open BadCover









end LonelyRunner.SeparatedBands

namespace LonelyRunner

open Finset



























end LonelyRunner

namespace LonelyRunner

















end LonelyRunner

namespace LonelyRunner.FailedWindow

open Farey BadCover









end LonelyRunner.FailedWindow

namespace LonelyRunner.SeparatedReplacements

open LargeDeletionMatching SeparatedBands























end LonelyRunner.SeparatedReplacements

namespace LonelyRunner.MixedReplacements

open LargeDeletionMatching SeparatedReplacements













end LonelyRunner.MixedReplacements

namespace LonelyRunner.SeparatedMulti

open SeparatedReplacements SeparatedBands SingleDeletion























end LonelyRunner.SeparatedMulti

namespace LonelyRunner.InteractionComponents

open Set























end LonelyRunner.InteractionComponents

namespace LonelyRunner.GWArithmetic

open SeparatedReplacements







end LonelyRunner.GWArithmetic

namespace LonelyRunner.ContactPreservation











end LonelyRunner.ContactPreservation

namespace LonelyRunner.GWContactArithmetic

open SeparatedReplacements ContactPreservation



















end LonelyRunner.GWContactArithmetic

namespace LonelyRunner.ComponentRestoration

open SeparatedMulti InteractionComponents









end LonelyRunner.ComponentRestoration

namespace LonelyRunner.GWGrowth

open SeparatedReplacements GWArithmetic

























end LonelyRunner.GWGrowth

namespace LonelyRunner.OddSmooth

open SeparatedReplacements GWGrowth















end LonelyRunner.OddSmooth

namespace LonelyRunner.SecondUnit

open SeparatedReplacements GWArithmetic OddSmooth











end LonelyRunner.SecondUnit

namespace LonelyRunner.ElementarySmooth

open SeparatedReplacements OddSmooth GWArithmetic GWGrowth SecondUnit

















end LonelyRunner.ElementarySmooth

namespace LonelyRunner.FailedFlank

open Farey BadCover LargeDeletionMatching









end LonelyRunner.FailedFlank

namespace LonelyRunner.FlankReduction

















end LonelyRunner.FlankReduction

namespace LonelyRunner.MixedNormalize

open SeparatedReplacements SecondUnit GWArithmetic



end LonelyRunner.MixedNormalize

namespace LonelyRunner.MixedArithmetic

open SeparatedReplacements GWArithmetic GWGrowth FlankReduction SecondUnit



end LonelyRunner.MixedArithmetic

namespace LonelyRunner.NearData

open LargeDeletionMatching SeparatedReplacements







end LonelyRunner.NearData

namespace LonelyRunner.MixedConverse

open LargeDeletionMatching SeparatedReplacements MixedReplacements
open GWArithmetic GWGrowth FlankReduction









end LonelyRunner.MixedConverse

namespace LonelyRunner.SmallComponentRigidity

open SeparatedMulti SeparatedReplacements InteractionComponents





































end LonelyRunner.SmallComponentRigidity

open LonelyRunner
open LonelyRunner.LaminarCover
open Set

/-- A connected covered set stays on the seed's side of a laminar cut,
provided no set on the other side contains the entire seed set. -/
theorem solution {ι X : Type*} [TopologicalSpace X]
    (T : Finset ι) (F : ι → Set X) (C : ι → Prop) [DecidablePred C]
    (hclosed : ∀ i ∈ T, IsClosed (F i))
    (hcross : ∀ i ∈ T, ∀ j ∈ T, C i → ¬ C j →
      (F i ∩ F j).Nonempty → F i ⊂ F j ∨ F j ⊂ F i)
    {S : Set X} (hconn : IsPreconnected S) (hcover : S ⊆ ⋃ i ∈ T, F i)
    {seed : ι} (hseed : seed ∈ T)
    (hno : ∀ j ∈ T, ¬ C j → ¬ F seed ⊆ F j)
    {x : X} (hxS : x ∈ S) (hxseed : x ∈ F seed) :
    S ⊆ ⋃ i ∈ T.filter C, F i := by
  classical
  let M := T.filter (fun i => ∀ j ∈ T, F i ⊆ F j → F j ⊆ F i)
  let A : Set X := ⋃ i ∈ M.filter C, F i
  let B : Set X := ⋃ i ∈ M.filter (fun i => ¬ C i), F i
  have hmem {i : ι} (hi : i ∈ M) :
      i ∈ T ∧ ∀ j ∈ T, F i ⊆ F j → F j ⊆ F i := Finset.mem_filter.mp hi
  have hAcl : IsClosed A := isClosed_biUnion_finset fun i hi =>
    hclosed i (hmem (Finset.mem_filter.mp hi).1).1
  have hBcl : IsClosed B := isClosed_biUnion_finset fun i hi =>
    hclosed i (hmem (Finset.mem_filter.mp hi).1).1
  have hdisjoint : Disjoint A B := by
    rw [Set.disjoint_left]
    intro y hyA hyB
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hyA
    obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hyB
    obtain ⟨hiM, hiC⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjM, hjC⟩ := Finset.mem_filter.mp hj
    obtain ⟨hiT, himax⟩ := hmem hiM
    obtain ⟨hjT, hjmax⟩ := hmem hjM
    rcases hcross i hiT j hjT hiC hjC ⟨y, hyi, hyj⟩ with h | h
    · exact (not_le_of_gt h) (himax j hjT h.le)
    · exact (not_le_of_gt h) (hjmax i hiT h.le)
  have hsub : S ⊆ A ∪ B := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (hcover hy)
    obtain ⟨j, hj, hij, hmax⟩ := exists_maximal_container T F hi
    have hjM : j ∈ M := Finset.mem_filter.mpr ⟨hj, hmax⟩
    by_cases hjC : C j
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr ⟨hjM,hjC⟩,hij hyi⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr ⟨hjM,hjC⟩,hij hyi⟩)
  have hxA : x ∈ A := by
    obtain ⟨j, hj, hij, hmax⟩ := exists_maximal_container T F hseed
    have hjC : C j := by
      by_contra hh
      exact hno j hj hh hij
    exact Set.mem_iUnion₂.mpr ⟨j,
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hj,hmax⟩,hjC⟩,hij hxseed⟩
  have hSA : S ⊆ A := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn
      A B hAcl hBcl hsub (by rw [hdisjoint.inter_eq, Set.inter_empty]) with h | h
    · exact h
    · exact False.elim (Set.disjoint_left.mp hdisjoint hxA (h hxS))
  intro y hy
  obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (hSA hy)
  obtain ⟨hiM, hiC⟩ := Finset.mem_filter.mp hi
  exact Set.mem_iUnion₂.mpr ⟨i,Finset.mem_filter.mpr ⟨(hmem hiM).1,hiC⟩,hyi⟩
