-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness.IsWachBasis.letter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:57:59.102959+00:00
-- url     : https://prove2.me/submissions/d2818d12-5558-4793-a1c7-e1f781635254

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_WachLettersFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
namespace GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness
namespace IsWachBasis
theorem _root_.solution {r : ℕ} {b : Fin r → W.DD T} (hb : IsWachBasis W T b) (i : ZMod n) :
    IsLetterBasis W T i (fun k => (letE i : LetA O n) • b k) := by
  obtain ⟨hli, hsp, -, -⟩ := hb
  have hmul : ∀ a : PowerSeries O,
      (Pi.single i a : LetA O n) * letE i = Pi.single i a := by
    intro a
    funext j
    by_cases h : j = i
    · subst h; simp [letE]
    · simp [letE, h]
  have hmul' : ∀ a : LetA O n, (letE i : LetA O n) * a = Pi.single i (a i) := by
    intro a
    funext j
    by_cases h : j = i
    · subst h; simp [letE]
    · simp [letE, h]
  refine ⟨fun k => ⟨b k, ?_, rfl⟩, ?_⟩
  · rw [← hsp]; exact Submodule.subset_span ⟨k, rfl⟩
  · rintro x ⟨y, hy, rfl⟩
    have hy' : y ∈ Submodule.span (LetA O n) (Set.range b) := by rw [hsp]; exact hy
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hy'
    have key : (letE i : LetA O n) • (∑ k, a k • b k) =
        ∑ k, (Pi.single i (a k i) : LetA O n) • b k := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, hmul']
    refine ⟨fun k => a k i, ?_, fun c hc => ?_⟩
    · change (letE i : LetA O n) • (∑ k, a k • b k) = _
      rw [key]
      exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, hmul]
    · change (letE i : LetA O n) • (∑ k, a k • b k) = _ at hc
      rw [key] at hc
      simp only [smul_smul, hmul] at hc
      funext k
      have h0 := Fintype.linearIndependent_iff.1 hli
        (fun k => (Pi.single i (c k) : LetA O n) - Pi.single i (a k i))
        (by simp only [sub_smul, Finset.sum_sub_distrib, hc, sub_self]) k
      have h1 := congrFun h0 i
      simpa [sub_eq_zero] using h1
end IsWachBasis
end GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness
