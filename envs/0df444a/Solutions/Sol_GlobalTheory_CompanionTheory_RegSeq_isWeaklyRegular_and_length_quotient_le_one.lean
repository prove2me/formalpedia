-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RegSeq.isWeaklyRegular_and_length_quotient_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:12:47.040774+00:00
-- url     : https://prove2.me/submissions/a24e7204-4010-4c46-9a5e-1a2cb0ee5a51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WeaklyRegularOfCotangentIndep
import Theorems.Thm_GlobalTheory_CompanionTheory_RegSeq_exists_ofList_append_eq_maximalIdeal
import Theorems.Thm_GlobalTheory_CompanionTheory_RegSeq_isWeaklyRegular_ofFn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing RingTheory.Sequence
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RegSeq
namespace GlobalTheory.CompanionTheory.RegSeq
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] (d : ℕ)
      (a : Fin d → R), ringKrullDim R ≤ d →
      LinearIndependent (ResidueField R) (fun j : {j : Fin d // a j ∈ maximalIdeal R} =>
        ((maximalIdeal R).toCotangent ⟨_, j.2⟩ : CotangentSpace R)) →
      RingTheory.Sequence.IsWeaklyRegular R (List.ofFn a) ∧
        Module.length R (R ⧸ Ideal.span (Set.range a)) ≤ 1 := by
  intro R _ _ _ _ d a hd hli
  classical
  by_cases hall : ∀ j, a j ∈ maximalIdeal R
  · have hli' : LinearIndependent (ResidueField R)
        (fun i => ((maximalIdeal R).toCotangent ⟨a i, hall i⟩ : CotangentSpace R)) :=
      hli.comp (fun i => ⟨i, hall i⟩) (fun i j h => congrArg Subtype.val h)
    refine ⟨isWeaklyRegular_ofFn a hall hli', ?_⟩
    obtain ⟨ys, h1, h2⟩ := exists_ofList_append_eq_maximalIdeal a hall hli'
    have hsf : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
      IsRegularLocalRing.spanFinrank_maximalIdeal
    have hle : (maximalIdeal R).spanFinrank ≤ d := by
      have h3 := hsf.trans_le hd
      exact_mod_cast h3
    have hys : ys = [] := by
      rw [List.length_append, List.length_ofFn] at h2
      apply List.eq_nil_of_length_eq_zero
      omega
    subst hys
    rw [List.append_nil] at h1
    have hspan : Ideal.span (Set.range a) = maximalIdeal R := by
      rw [← h1]
      unfold Ideal.ofList
      congr 1
      ext x
      exact List.mem_ofFn.symm
    rw [hspan]
    have hs : IsSimpleModule R (R ⧸ maximalIdeal R) :=
      isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (maximalIdeal.isMaximal R))
    exact (Module.length_eq_one_iff.mpr hs).le
  · push_neg at hall
    obtain ⟨j1, hj1⟩ := hall
    have hex : ∃ n, ∃ h : n < d, a ⟨n, h⟩ ∉ maximalIdeal R := ⟨j1.val, j1.isLt, hj1⟩
    obtain ⟨n, hn, han, hmin⟩ : ∃ n, ∃ hn : n < d, a ⟨n, hn⟩ ∉ maximalIdeal R ∧
        ∀ k (hk : k < n), a ⟨k, lt_trans hk hn⟩ ∈ maximalIdeal R := by
      refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun k hk => ?_⟩
      by_contra hc
      exact Nat.find_min hex hk ⟨lt_trans hk (Nat.find_spec hex).1, hc⟩
    have hu : IsUnit (a ⟨n, hn⟩) := by
      by_contra h
      exact han ((mem_maximalIdeal _).2 (mem_nonunits_iff.2 h))
    have htop : ∀ i, n < i → Ideal.ofList ((List.ofFn a).take i) = ⊤ := by
      intro i hi
      apply Ideal.eq_top_of_isUnit_mem _ _ hu
      apply Ideal.subset_span
      show a ⟨n, hn⟩ ∈ (List.ofFn a).take i
      refine List.mem_take_iff_getElem.mpr ⟨n, ?_, ?_⟩
      · rw [List.length_ofFn]
        exact lt_min hi hn
      · rw [List.getElem_ofFn]
    have hsub : ∀ (N : Submodule R R), N = ⊤ → ∀ r : R, IsSMulRegular (R ⧸ N) r := by
      rintro N rfl r x y _
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact (Submodule.Quotient.eq _).2 Submodule.mem_top
    have hpre : IsWeaklyRegular R (List.ofFn (fun k : Fin n => a ⟨k, lt_trans k.2 hn⟩)) :=
      isWeaklyRegular_ofFn _ (fun k => hmin k k.2)
        (hli.comp (fun k : Fin n => ⟨⟨k, lt_trans k.2 hn⟩, hmin k k.2⟩) (fun x y h => by
          have h5 := congrArg (fun z : {j : Fin d // a j ∈ maximalIdeal R} => (z.1 : Fin d).val) h
          exact Fin.ext h5))
    have hpre' : List.ofFn (fun k : Fin n => a ⟨k, lt_trans k.2 hn⟩) = (List.ofFn a).take n := by
      apply List.ext_getElem
      · simp only [List.length_ofFn, List.length_take]
        omega
      · intro i h1 h2
        simp [List.getElem_ofFn, List.getElem_take]
    refine ⟨(isWeaklyRegular_iff R _).2 (fun i hi => ?_), ?_⟩
    · rw [List.length_ofFn] at hi
      rcases lt_trichotomy i n with h | h | h
      · have hg := (isWeaklyRegular_iff R _).1 hpre i (by rw [List.length_ofFn]; exact h)
        have e1 : (List.ofFn a).take i =
            (List.ofFn (fun k : Fin n => a ⟨k, lt_trans k.2 hn⟩)).take i := by
          rw [hpre', List.take_take, min_eq_left h.le]
        rw [e1]
        simp only [List.getElem_ofFn] at hg ⊢
        exact hg
      · subst h
        simp only [List.getElem_ofFn]
        exact IsUnit.isSMulRegular _ hu
      · exact hsub _ (by rw [htop i h, Submodule.top_smul]) _
    · have hspan : Ideal.span (Set.range a) = ⊤ :=
        Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨⟨n, hn⟩, rfl⟩) hu
      rw [hspan]
      have hss : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      rw [Module.length_eq_zero_iff.mpr hss]
      exact zero_le_one
end GlobalTheory.CompanionTheory.RegSeq
