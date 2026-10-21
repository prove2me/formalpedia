-- Prove2me | solution 1 for HyperKCut.Structure.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T15:08:55.357995+00:00
-- url     : https://prove2.me/submissions/a1c14ab4-96d8-464b-97e9-99e8d537e154

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model
import Theorems.Thm_HyperKCut_Structure_theorem_3_1
import Theorems.Thm_HyperKCut_Structure_lemma_4_1
import Theorems.Thm_HyperKCut_Structure_claim_4_2
import Theorems.Thm_HyperKCut_Structure_source_max_cut

open HyperKCut.Structure

theorem solution {V : Type} [Fintype V] [DecidableEq V] (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) [NeZero k]
    (hk : 2 ≤ k)
    (P : Fin k → Finset V) (hP : IsMaximalMinKPartition H k P)
    (hV1 : 2 * k - 2 ≤ (P 0).card)
    (T : Finset V) (hT : T ⊆ (P 0)ᶜ)
    (hTj : ∀ j : Fin k, j ≠ 0 → (T ∩ P j).Nonempty) :
    ∃ S : Finset V, S ⊆ P 0 ∧ S.card = 2 * k - 2 ∧
      IsSourceMaxMinTerminalCut H S T (P 0) := by
  classical
  -- symmetry of the cut function
  have dsym : ∀ A : Finset V, d H Aᶜ = d H A := by
    intro A
    unfold d
    congr 1
    apply Multiset.filter_congr
    intro e _
    simp only [compl_compl]
    exact and_comm
  -- disjointness of subsets of `P 0` from `T`
  have hdisj : ∀ X : Finset V, X ⊆ P 0 → Disjoint X T := by
    intro X hX
    rw [Finset.disjoint_left]
    intro v hv hvT
    have := hT hvT
    rw [Finset.mem_compl] at this
    exact this (hX hv)
  -- the source-maximal cut as a function of the source set
  let VX : Finset V → Finset V := fun X =>
    if h : ∃ U, IsSourceMaxMinTerminalCut H X T U then h.choose else ∅
  have hVX : ∀ X, X ⊆ P 0 → IsSourceMaxMinTerminalCut H X T (VX X) := by
    intro X hX
    have h : ∃ U, IsSourceMaxMinTerminalCut H X T U :=
      (source_max_cut H X T (hdisj X hX)).1.exists
    simp only [VX, dif_pos h]
    exact h.choose_spec
  have huniq : ∀ X U, X ⊆ P 0 → IsSourceMaxMinTerminalCut H X T U → U = VX X := by
    intro X U hX hU
    exact (source_max_cut H X T (hdisj X hX)).1.unique hU (hVX X hX)
  -- pick S maximizing d(V_S)
  set F := (P 0).powersetCard (2 * k - 2) with hF
  have hFne : F.Nonempty := Finset.powersetCard_nonempty.mpr hV1
  obtain ⟨S, hSF, hSmax⟩ := Finset.exists_max_image F (fun X => d H (VX X)) hFne
  rw [Finset.mem_powersetCard] at hSF
  obtain ⟨hSP, hScard⟩ := hSF
  by_cases hdone : IsSourceMaxMinTerminalCut H S T (P 0)
  · exact ⟨S, hSP, hScard, hdone⟩
  exfalso
  set VS := VX S with hVSdef
  have hVS : IsSourceMaxMinTerminalCut H S T VS := hVX S hSP
  have hmax : ∀ (X VX' : Finset V), X ⊆ P 0 → X.card = 2 * k - 2 →
      IsSourceMaxMinTerminalCut H X T VX' → d H VX' ≤ d H VS := by
    intro X VX' hX hXc hXV
    rw [huniq X VX' hX hXV]
    exact hSmax X (Finset.mem_powersetCard.mpr ⟨hX, hXc⟩)
  have hVSsub : VS ⊆ P 0 := lemma_4_1 H k hk P hP S T hSP hT hTj VS hVS.1
  have hVSne : VS ≠ P 0 := by
    intro h
    apply hdone
    rw [← h]
    exact hVS
  have hss : VS ⊂ P 0 := Finset.ssubset_iff_subset_ne.mpr ⟨hVSsub, hVSne⟩
  obtain ⟨w, hwP, hwVS⟩ := Finset.exists_of_ssubset hss
  -- d(V_S) < d(V_1)
  have hP0term : IsTerminalCut S T (P 0) := ⟨hSP, hdisj (P 0) le_rfl⟩
  have hlt : d H VS < d H (P 0) := by
    have hle : d H VS ≤ d H (P 0) := hVS.1.2 (P 0) hP0term
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have hmin : IsMinTerminalCut H S T (P 0) := by
        refine ⟨hP0term, fun U' hU' => ?_⟩
        rw [← h]
        exact hVS.1.2 U' hU'
      exact hVSne (Finset.Subset.antisymm hVSsub (hVS.2 (P 0) hmin))
  -- d(V_1) ≤ cost(P)
  have hPpart := hP.1.1
  have hd0 : d H (P 0) ≤ cost H P := by
    unfold d cost
    apply Multiset.card_le_card
    apply Multiset.monotone_filter_right
    intro e he
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := he
    rw [Finset.mem_inter] at hx hy
    obtain ⟨j, hj⟩ := hPpart.2.2 y
    have hj0 : j ≠ 0 := by
      intro h
      subst h
      exact (Finset.mem_compl.mp hy.2) hj
    exact ⟨0, j, hj0.symm, ⟨x, Finset.mem_inter.mpr hx⟩, ⟨y, Finset.mem_inter.mpr ⟨hy.1, hj⟩⟩⟩
  -- enumerate S
  set p := 2 * k - 2 with hp
  have hp2 : 2 ≤ p := by omega
  let eS := S.equivFin
  let u : Fin p → V := fun i => (eS.symm (Fin.cast hScard.symm i) : V)
  have huinj : Function.Injective u := by
    intro i j hij
    have h1 : eS.symm (Fin.cast hScard.symm i) = eS.symm (Fin.cast hScard.symm j) :=
      Subtype.ext hij
    have h2 := eS.symm.injective h1
    exact Fin.cast_injective _ h2
  have huS : ∀ i, u i ∈ S := fun i => (eS.symm (Fin.cast hScard.symm i)).2
  have himage : Finset.univ.image u = S := by
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact huS i
    · intro hv
      refine ⟨Fin.cast hScard (eS ⟨v, hv⟩), ?_⟩
      simp [u]
  have hwS : w ∉ S := fun h => hwVS (hVS.1.1.1 h)
  have hCsub : ∀ x, x ∈ insert w S → x ∈ P 0 := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hwP
    · exact hSP hx
  -- the cuts B_i
  let C : Fin p → Finset V := fun i => (insert w S).erase (u i)
  have hCP : ∀ i, C i ⊆ P 0 := fun i x hx => hCsub x (Finset.mem_of_mem_erase hx)
  have hCcard : ∀ i, (C i).card = 2 * k - 2 := by
    intro i
    simp only [C]
    rw [Finset.card_erase_of_mem (Finset.mem_insert_of_mem (huS i)),
      Finset.card_insert_of_notMem hwS, hScard]
    omega
  let B : Fin p → Finset V := fun i => VX (C i)
  have hB : ∀ i, IsSourceMaxMinTerminalCut H (C i) T (B i) := fun i => hVX (C i) (hCP i)
  have hBP : ∀ i, B i ⊆ P 0 := fun i =>
    lemma_4_1 H k hk P hP (C i) T (hCP i) hT hTj (B i) (hB i).1
  have hBle : ∀ i, d H (B i) ≤ d H VS := fun i => hmax (C i) (B i) (hCP i) (hCcard i) (hB i)
  have hCeq : ∀ i, ((Finset.univ.image u) ∪ {w}).erase (u i) = C i := by
    intro i
    rw [himage]
    simp only [C]
    congr 1
    ext v
    simp
  -- hypotheses of Theorem 3.1
  let A : Fin p → Finset V := fun i => (B i)ᶜ
  have hA : ∀ i, IsMinTerminalCut H (((Finset.univ.image u) ∪ {w}).erase (u i)) (P 0)ᶜ (A i)ᶜ := by
    intro i
    rw [hCeq i]
    simp only [A, compl_compl]
    refine ⟨⟨(hB i).1.1.1, ?_⟩, ?_⟩
    · rw [Finset.disjoint_left]
      intro v hv hv'
      exact (Finset.mem_compl.mp hv') (hBP i hv)
    · intro U' hU'
      apply (hB i).1.2 U'
      refine ⟨hU'.1, ?_⟩
      exact Disjoint.mono_right hT hU'.2
  have hui : ∀ i, u i ∈ A i := by
    intro i
    simp only [A]
    rw [Finset.mem_compl]
    exact claim_4_2 H k hk P hP T hT hTj S VS hSP hScard hVS hmax w
      (Finset.mem_sdiff.mpr ⟨hwP, hwVS⟩) (u i) (Finset.mem_insert_of_mem (huS i)) (B i) (hB i)
  have huj : ∀ i j, i ≠ j → u i ∉ A j := by
    intro i j hij
    simp only [A]
    rw [Finset.mem_compl, not_not]
    apply (hB j).1.1.1
    simp only [C]
    rw [Finset.mem_erase]
    exact ⟨fun h => hij (huinj h), Finset.mem_insert_of_mem (huS i)⟩
  have hu : ∀ i, u i ∈ P 0 \ {w} := by
    intro i
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    refine ⟨hSP (huS i), ?_⟩
    intro h
    apply hwVS
    rw [← h]
    exact hVS.1.1.1 (huS i)
  have hR : ({w} : Finset V).Nonempty := Finset.singleton_nonempty w
  have hRU : ({w} : Finset V) ⊂ P 0 := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.singleton_subset_iff.mpr hwP, ?_⟩
    intro h
    have : (P 0).card = 1 := by rw [← h]; simp
    omega
  have hUV : P 0 ⊂ (Finset.univ : Finset V) := by
    rw [Finset.ssubset_univ_iff]
    intro h
    have h1 : (⟨1, by omega⟩ : Fin k) ≠ 0 := by
      intro h'
      have := congrArg Fin.val h'
      simp at this
    obtain ⟨v, hv⟩ := hPpart.1 ⟨1, by omega⟩
    have hd := hPpart.2.1 ⟨1, by omega⟩ 0 h1
    rw [h] at hd
    exact Finset.disjoint_left.mp hd hv (Finset.mem_univ v)
  obtain ⟨P', hP', -, hcost⟩ := theorem_3_1 H k p hk le_rfl {w} (P 0) hR hRU hUV u huinj hu A hA
    hui huj
  have h01 : (⟨0, by omega⟩ : Fin p) ≠ ⟨1, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hc := hcost ⟨0, by omega⟩ ⟨1, by omega⟩ h01
  simp only [A, dsym] at hc
  have hb0 := hBle ⟨0, by omega⟩
  have hb1 := hBle ⟨1, by omega⟩
  have hopt := hP.1.2 P' hP'
  omega
