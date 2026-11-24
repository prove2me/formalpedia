-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RootExch.rootExchange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:39:42.84155+00:00
-- url     : https://prove2.me/submissions/ddec7775-d06f-440a-9af6-f1929f13aeb6

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchange
import Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_exchange
import Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_nz_of_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_patSet_mono
import Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_exists_twist
import Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_card_pairs
import Theorems.Thm_GlobalTheory_CompanionTheory_PatGrp_patGroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RootExch
namespace GlobalTheory.CompanionTheory.RootExch
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.RootExchange := by
  intro K _ _ _ ι _ _ Φ E ψ₀ W p q χ hΦ hψ hχ h1 hEpq hsupp hEW hc1 hc2 hcomp
  have hcomp' : ∀ i j k, Φ i j → Φ j k → E i k ≠ 0 → i = p ∧ k = q :=
    fun i j k a b c => ⟨(hcomp i j k a b c).1, (hcomp i j k a b c).2.1⟩
  have pat1 : IsPat (fun i j => Φ i j ∧ ¬ (W i ∧ j = q)) := by
    refine ⟨fun i h => hΦ.1 i h.1, fun i j k hij hjk => ⟨hΦ.2 _ _ _ hij.1 hjk.1, ?_⟩⟩
    rintro ⟨hWi, rfl⟩
    exact hjk.2 ⟨hc1 i j hWi hij.1 hjk.1, rfl⟩
  have pat2 : IsPat (fun i j => Φ i j ∧ ¬ (i = p ∧ W j)) := by
    refine ⟨fun i h => hΦ.1 i h.1, fun i j k hij hjk => ⟨hΦ.2 _ _ _ hij.1 hjk.1, ?_⟩⟩
    rintro ⟨rfl, hWk⟩
    exact hij.2 ⟨rfl, hc2 k j hWk hij.1 hjk.1⟩
  have char1 : IsPatChar (fun i j => Φ i j ∧ ¬ (W i ∧ j = q)) E := by
    refine ⟨fun i j hE => ⟨hsupp i j hE, ?_⟩, fun i j k hij hjk => ?_⟩
    · rintro ⟨hW, rfl⟩
      exact hE (hEW i hW).2
    · by_contra hE
      obtain ⟨_, hk, hWj⟩ := hcomp i j k hij.1 hjk.1 hE
      exact hjk.2 ⟨hWj, hk⟩
  have char2 : IsPatChar (fun i j => Φ i j ∧ ¬ (i = p ∧ W j)) E := by
    refine ⟨fun i j hE => ⟨hsupp i j hE, ?_⟩, fun i j k hij hjk => ?_⟩
    · rintro ⟨rfl, hW⟩
      exact hE (hEW j hW).1
    · by_contra hE
      obtain ⟨hi, _, hWj⟩ := hcomp i j k hij.1 hjk.1 hE
      exact hij.2 ⟨hi, hWj⟩
  obtain ⟨⟨P, hP⟩, cardP, hcharP⟩ := GlobalTheory.CompanionTheory.PatGrp.patGroup K ι _ pat1
  obtain ⟨⟨Q, hQ⟩, cardQ, hcharQ⟩ := GlobalTheory.CompanionTheory.PatGrp.patGroup K ι _ pat2
  have mulP := (hcharP E ψ₀ char1).1
  have mulQ := (hcharQ E ψ₀ char2).1
  have memP : ∀ u, u ∈ P ↔ u ∈ patSet K (fun i j => Φ i j ∧ ¬ (W i ∧ j = q)) := fun u => by
    rw [← hP]; rfl
  have memQ : ∀ u, u ∈ Q ↔ u ∈ patSet K (fun i j => Φ i j ∧ ¬ (i = p ∧ W j)) := fun u => by
    rw [← hQ]; rfl
  have hne : ∀ u : GL ι K, patChar E ψ₀ u ≠ 0 := fun u => (ψ₀.val_isUnit _).ne_zero
  have hsum := exchange P Q (patChar E ψ₀) χ hχ
    (fun a ha b hb => mulP a ((memP a).1 ha) b ((memP b).1 hb)) (fun a _ => hne a)
    (fun a ha b hb => mulQ a ((memQ a).1 ha) b ((memQ b).1 hb)) (fun a _ => hne a)
    (by
      intro v hvQ hvP
      have vQ := (memQ v).1 hvQ
      have viQ := (memQ _).1 (Q.inv_mem hvQ)
      have viP : v⁻¹ ∉ patSet K (fun i j => Φ i j ∧ ¬ (W i ∧ j = q)) := fun h =>
        hvP (by simpa using P.inv_mem ((memP _).2 h))
      obtain ⟨w, hw, hnz⟩ : ∃ w, W w ∧ ((v⁻¹ : GL ι K) : Matrix ι ι K) w q ≠ 0 := by
        by_contra hc
        push_neg at hc
        apply viP
        intro i j
        refine ⟨(viQ i j).1, fun hij hn => ?_⟩
        by_contra hx
        rcases nz_of_mem viQ hx with h | h
        · exact hij h
        · have h3 : W i ∧ j = q := by
            by_contra h'
            exact hn ⟨h.1, h'⟩
          obtain ⟨hWi, rfl⟩ := h3
          exact hx (hc i hWi)
      obtain ⟨h, hh, hc, hl⟩ := exists_twist (Ψ := fun i j => Φ i j ∧ ¬ (W i ∧ j = q)) ψ₀ hψ hΦ hsupp p q p w hcomp' v
        (patSet_mono (fun _ _ h => h.1) vQ) (patSet_mono (fun _ _ h => h.1) viQ) (h1 w hw).1
        ⟨(h1 w hw).1, fun hh => hΦ.1 p (h1 p hh.1).1⟩
        (by
          intro i j hi hj hn
          refine ⟨?_, fun hh => ?_⟩
          · rcases hi with rfl | hi <;> rcases hj with rfl | hj
            · exact absurd ⟨rfl, rfl⟩ hn
            · exact hΦ.2 _ _ _ (h1 w hw).1 hj
            · exact hΦ.2 _ _ _ hi (h1 _ hw).1
            · exact hΦ.2 _ _ _ hi (hΦ.2 _ _ _ (h1 w hw).1 hj)
          · rcases hi with rfl | hi
            · exact hΦ.1 _ (h1 _ hh.1).1
            · exact hΦ.1 _ (hΦ.2 _ _ _ hi (h1 _ hh.1).1))
        (hEW w hw).1 hEpq
        (by rw [(vQ p p).1 rfl, one_mul]; exact hnz)
      exact ⟨h, (memP _).2 hh, (memP _).2 hc, hl⟩)
    (by
      intro v hvP hvQ
      have vP := (memP v).1 hvP
      have viP := (memP _).1 (P.inv_mem hvP)
      have vQ' : v ∉ patSet K (fun i j => Φ i j ∧ ¬ (i = p ∧ W j)) := fun h => hvQ ((memQ v).2 h)
      obtain ⟨w, hw, hnz⟩ : ∃ w, W w ∧ (v : Matrix ι ι K) p w ≠ 0 := by
        by_contra hc
        push_neg at hc
        apply vQ'
        intro i j
        refine ⟨(vP i j).1, fun hij hn => ?_⟩
        by_contra hx
        rcases nz_of_mem vP hx with h | h
        · exact hij h
        · have h3 : i = p ∧ W j := by
            by_contra h'
            exact hn ⟨h.1, h'⟩
          obtain ⟨rfl, hWj⟩ := h3
          exact hx (hc j hWj)
      obtain ⟨h, hh, hc, hl⟩ := exists_twist (Ψ := fun i j => Φ i j ∧ ¬ (i = p ∧ W j)) ψ₀ hψ hΦ hsupp p q w q hcomp' v
        (patSet_mono (fun _ _ h => h.1) vP) (patSet_mono (fun _ _ h => h.1) viP) (h1 w hw).2
        ⟨(h1 w hw).2, fun hh => hΦ.1 q (h1 q hh.2).2⟩
        (by
          intro i j hi hj hn
          refine ⟨?_, fun hh => ?_⟩
          · rcases hi with rfl | hi <;> rcases hj with rfl | hj
            · exact absurd ⟨rfl, rfl⟩ hn
            · exact hΦ.2 _ _ _ (h1 _ hw).2 hj
            · exact hΦ.2 _ _ _ hi (h1 w hw).2
            · exact hΦ.2 _ _ _ hi (hΦ.2 _ _ _ (h1 w hw).2 hj)
          · rcases hj with rfl | hj
            · exact hΦ.1 _ (h1 _ hh.2).2
            · exact hΦ.1 _ (hΦ.2 _ _ _ hj (h1 _ hh.2).2))
        (hEW w hw).2 hEpq
        (by rw [(viP q q).1 rfl, mul_one]; exact hnz)
      exact ⟨h, (memQ _).2 hh, (memQ _).2 hc, hl⟩)
  have hcard : (patSet K (fun i j => Φ i j ∧ ¬ (W i ∧ j = q))).ncard =
      (patSet K (fun i j => Φ i j ∧ ¬ (i = p ∧ W j))).ncard := by
    rw [cardP, cardQ]
    congr 1
    exact card_pairs Φ W p q h1
  unfold wh
  rw [hcard]
  congr 1
  refine (Finset.sum_congr rfl fun u _ => ?_).trans (hsum.trans (Finset.sum_congr rfl fun u _ => ?_))
  · by_cases h : u ∈ P
    · rw [if_pos h, if_pos ((memP u).1 h)]
    · rw [if_neg h, if_neg (fun h' => h ((memP u).2 h'))]
  · by_cases h : u ∈ Q
    · rw [if_pos h, if_pos ((memQ u).1 h)]
    · rw [if_neg h, if_neg (fun h' => h ((memQ u).2 h'))]
end GlobalTheory.CompanionTheory.RootExch
