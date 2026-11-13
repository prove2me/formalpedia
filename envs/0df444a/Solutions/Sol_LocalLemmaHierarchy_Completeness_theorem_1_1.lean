-- Prove2me | solution 1 for LocalLemmaHierarchy.Completeness.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:28:54.034017+00:00
-- url     : https://prove2.me/submissions/857e0df4-888b-4265-b38d-40c28aa120cf

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Definitions.Def_LocalLemmaHierarchy_Completeness_Histories
import Definitions.Def_LocalLemmaHierarchy_Completeness_Memory
import Definitions.Def_LocalLemmaHierarchy_Completeness_Graph
import Theorems.Thm_LocalLemmaHierarchy_Completeness_theorem_3_2
import Theorems.Thm_LocalLemmaHierarchy_Completeness_theorem_3_7
import Theorems.Thm_LocalLemmaHierarchy_Completeness_theorem_3_9
import Theorems.Thm_LocalLemmaHierarchy_Completeness_proposition_3_10
import Theorems.Thm_LocalLemmaHierarchy_Completeness_memory_zero_lll
import Theorems.Thm_LocalLemmaHierarchy_Completeness_theorem_2_3

section
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness.Dev.MZ

open scoped Classical

variable {V : Type} (G : SimpleGraph V) [G.LocallyFinite] (o : NeighborOrders G)

theorem sum_helper {ι M : Type} [AddCommMonoid M] [Fintype ι] [Subsingleton ι] (a0 : ι)
    (s : Finset ι) (hs : a0 ∈ s) (f : ι → M) : ∑ a ∈ s, f a = f a0 :=
  Finset.sum_eq_single_of_mem a0 hs (fun b _ hb => absurd (Subsingleton.elim b a0) hb)

theorem indep_insert (J : Finset V) (v : V) :
    G.IsIndepSet (↑(insert v J) : Set V) ↔
      G.IsIndepSet (↑J : Set V) ∧ ∀ w ∈ J, v ≠ w → ¬ G.Adj v w := by
  rw [SimpleGraph.isIndepSet_iff, SimpleGraph.isIndepSet_iff, Finset.coe_insert,
    Set.pairwise_insert]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun w hw hne => (h2 w hw hne).1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun w hw hne => ⟨h2 w hw hne, fun hh => h2 w hw hne hh.symm⟩⟩

theorem indep_split (U : Finset V) (v : V) (hv : v ∈ U) :
    indepPoly G U = indepPoly G (U.erase v) +
      MvPolynomial.X v * indepPoly G (U \ insert v (G.neighborFinset v)) := by
  unfold indepPoly
  rw [← Finset.sum_filter_add_sum_filter_not
    (U.powerset.filter (fun I : Finset V => G.IsIndepSet (I : Set V))) (fun I => v ∈ I)]
  have h1 : (U.powerset.filter (fun I : Finset V => G.IsIndepSet (I : Set V))).filter
      (fun I => ¬ v ∈ I) = (U.erase v).powerset.filter (fun I : Finset V => G.IsIndepSet (I : Set V)) := by
    ext I
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨fun w hw => Finset.mem_erase.2 ⟨fun e => h3 (e ▸ hw), h1 hw⟩, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨fun w hw => (Finset.mem_erase.1 (h1 hw)).2, h2⟩, fun hh => ?_⟩
      exact (Finset.mem_erase.1 (h1 hh)).1 rfl
  have h2 : (U.powerset.filter (fun I : Finset V => G.IsIndepSet (I : Set V))).filter
      (fun I => v ∈ I) = ((U \ insert v (G.neighborFinset v)).powerset.filter
        (fun I : Finset V => G.IsIndepSet (I : Set V))).image (insert v) := by
    ext I
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨I.erase v, ⟨?_, ?_⟩, Finset.insert_erase h3⟩
      · have h2' := h2
        rw [← Finset.insert_erase h3, indep_insert] at h2'
        intro w hw
        obtain ⟨hne, hwI⟩ := Finset.mem_erase.1 hw
        simp only [Finset.mem_sdiff, Finset.mem_insert, not_or, SimpleGraph.mem_neighborFinset]
        exact ⟨h1 hwI, fun e => hne e, fun hadj => h2'.2 w hw (Ne.symm hne) hadj⟩
      · have h2' := h2
        rw [← Finset.insert_erase h3, indep_insert] at h2'
        exact h2'.1
    · rintro ⟨J, ⟨h1, h2⟩, rfl⟩
      have hvJ : v ∉ J := fun hh => by
        have := h1 hh
        simp at this
      refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
      · intro w hw
        rcases Finset.mem_insert.1 hw with rfl | hw
        · exact hv
        · exact (Finset.mem_sdiff.1 (h1 hw)).1
      · rw [indep_insert]
        refine ⟨h2, fun w hw _ hadj => ?_⟩
        have := (Finset.mem_sdiff.1 (h1 hw)).2
        simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or] at this
        exact this.2 hadj
  rw [h1, h2, Finset.sum_image, Finset.mul_sum, add_comm]
  · congr 1
    refine Finset.sum_congr rfl fun J hJ => ?_
    have hvJ : v ∉ J := by
      simp only [Finset.mem_filter, Finset.mem_powerset] at hJ
      intro hh
      have := hJ.1 hh
      simp at this
    rw [Finset.prod_insert hvJ]
  · intro I hI J hJ hIJ
    have hvI : v ∉ I := by
      simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq] at hI
      intro hh
      have := hI.1 hh
      simp at this
    have hvJ : v ∉ J := by
      simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq] at hJ
      intro hh
      have := hJ.1 hh
      simp at this
    rw [← Finset.erase_insert hvI, hIJ, Finset.erase_insert hvJ]

theorem indep_rep : IsRepresentationOf (indRep G o) (indepPoly G) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold indepPoly
    rw [Finset.powerset_empty, Finset.filter_singleton, if_pos (by simp [SimpleGraph.isIndepSet_iff])]
    simp
  · intro U
    unfold indepPoly
    rw [map_sum, Finset.sum_eq_single ∅]
    · simp
    · intro I hI hne
      rw [map_prod]
      obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.2 hne
      exact Finset.prod_eq_zero hw (by simp)
    · intro h
      exfalso
      apply h
      simp
  · intro U v hv
    have hfil : Finset.univ.filter (fun a : (indRep G o).Opt v =>
        (indRep G o).A v a ⊆ U) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro a _
      show ({v} : Finset V) ⊆ U
      simpa using hv
    rw [hfil]
    have : Subsingleton ((indRep G o).Opt v) := inferInstanceAs (Subsingleton Unit)
    rw [indep_split G U v hv]
    congr 1
    refine Eq.symm ((sum_helper (ι := (indRep G o).Opt v) () _ (Finset.mem_univ _) _).trans ?_)
    show MvPolynomial.C (1 : ℝ) * MvPolynomial.X v *
      indepPoly G (U \ insert v (G.neighborFinset v)) = _
    rw [map_one, one_mul]

end LocalLemmaHierarchy.Completeness.Dev.MZ

namespace LocalLemmaHierarchy.Completeness

end LocalLemmaHierarchy.Completeness
end

section
set_option autoImplicit false

open scoped ENNReal NNReal
open Filter Topology

namespace LocalLemmaHierarchy.Completeness.Dev.T11

open LocalLemmaHierarchy.Completeness

theorem shearer_eq {V : Type} (G : SimpleGraph V) [G.LocallyFinite] (o : NeighborOrders G) :
    shearerThreshold G = uniformRadius (indepPoly G) := by
  classical
  unfold shearerThreshold uniformRadius
  refine iInf_congr fun U => ?_
  unfold regionRadius
  refine iSup_congr fun t => iSup_congr_Prop ?_ fun _ => rfl
  have h := (theorem_2_3 (indRep G o) (indepPoly G) (MZ.indep_rep G o) U (fun _ => (t : ℝ))
    (fun _ => t.2)).1
  exact (h.trans Iff.rfl).symm

theorem cstar_eq {V : Type} [Nonempty V] (G : SimpleGraph V) [G.LocallyFinite]
    (o : NeighborOrders G) : (indRep G o).cstar = 1 := by
  have : Nonempty (Σ v : V, (indRep G o).Opt v) := ⟨⟨Classical.arbitrary V, ()⟩⟩
  unfold PosLocalDeletionRep.cstar
  exact ciInf_const

theorem nonconst {V : Type} [Nonempty V] (G : SimpleGraph V) [G.LocallyFinite]
    (o : NeighborOrders G) : IsNonconstant (indepPoly G) := by
  have := (theorem_3_7 (indRep G o) (indepPoly G) (MZ.indep_rep G o)).2.2.1
  exact this.mpr ⟨Classical.arbitrary V, ⟨()⟩⟩

theorem part1 {V : Type} [Nonempty V] (G : SimpleGraph V) [G.LocallyFinite]
    (o : NeighborOrders G) :
    Monotone (lambdaQ G o) ∧ (∀ q, lambdaQ G o q ≤ shearerThreshold G) ∧
      Tendsto (lambdaQ G o) atTop (𝓝 (shearerThreshold G)) := by
  have h := theorem_3_7 (indRep G o) (indepPoly G) (MZ.indep_rep G o)
  rw [shearer_eq G o]
  exact ⟨h.1, fun q => h.1.ge_of_tendsto h.2.1 q, h.2.1⟩

theorem part2b {V : Type} [Nonempty V] (G : SimpleGraph V) [G.LocallyFinite]
    (o : NeighborOrders G) :
    lambdaQ G o 0 =
        ⨆ (t : ℝ≥0) (_ : ∃ x : V → ℝ, ∀ v, 0 ≤ x v ∧ x v < 1 ∧
            (t : ℝ) ≤ x v * ∏ u ∈ G.neighborFinset v, (1 - x u)), (t : ℝ≥0∞) := by
  unfold lambdaQ memRadius
  refine iSup_congr fun t => iSup_congr_Prop ?_ fun _ => rfl
  have hm := (memory_zero_lll G o (fun _ => (t : ℝ)) (fun _ => t.2)).1
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨fun v => x (indState G o v), (hm x).1 hx⟩
  · rintro ⟨y, hy⟩
    refine ⟨fun s => y s.endpoint, (hm _).2 fun v => ?_⟩
    simpa [indState, Hist.endpoint, Hist.endpointOf] using hy v

theorem part3 {V : Type} [Nonempty V] (G : SimpleGraph V) [G.LocallyFinite]
    (o : NeighborOrders G) (q : ℕ) (hq : 1 ≤ q) :
    lambdaQ G o q ≤ shearerThreshold G ∧
      shearerThreshold G ≤
        lambdaQ G o q + ENNReal.ofReal (min (1 / (q : ℝ)) (Real.pi ^ 2 / ((q : ℝ) + 1) ^ 2)) := by
  refine ⟨(part1 G o).2.1 q, ?_⟩
  have hrep := MZ.indep_rep G o
  have h7 := theorem_3_7 (indRep G o) (indepPoly G) hrep
  have h9 := theorem_3_9 (indRep G o) (indepPoly G) hrep (nonconst G o) q hq
  have hc := cstar_eq G o
  rw [shearer_eq G o]
  have hnc := nonconst G o
  obtain ⟨hle, h7q⟩ := h7.2.2.2 hnc
  obtain ⟨h7a, -⟩ := h7q q hq
  rw [hc] at hle h7a
  have hfin : uniformRadius (indepPoly G) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have A : uniformRadius (indepPoly G) ≤
      lambdaQ G o q + ENNReal.ofReal (1 / (q : ℝ)) := by
    calc uniformRadius (indepPoly G)
        = ENNReal.ofReal (uniformRadius (indepPoly G)).toReal :=
          (ENNReal.ofReal_toReal hfin).symm
      _ ≤ ENNReal.ofReal ((uniformRadius (indepPoly G)).toReal - 1 / (1 * (q : ℝ))
            + 1 / (q : ℝ)) := by
          apply ENNReal.ofReal_le_ofReal; simp
      _ ≤ ENNReal.ofReal ((uniformRadius (indepPoly G)).toReal - 1 / (1 * (q : ℝ)))
            + ENNReal.ofReal (1 / (q : ℝ)) := ENNReal.ofReal_add_le
      _ ≤ _ := by
          unfold lambdaQ; gcongr
  have B : uniformRadius (indepPoly G) ≤
      lambdaQ G o q + ENNReal.ofReal (Real.pi ^ 2 / ((q : ℝ) + 1) ^ 2) := by
    refine h9.2.1.2.trans ?_
    rw [hc]
    have := h9.1
    rw [hc, one_mul, div_one] at this
    unfold lambdaQ
    rw [div_one]
    exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal this)
  rcases min_choice (1 / (q : ℝ)) (Real.pi ^ 2 / ((q : ℝ) + 1) ^ 2) with h | h <;> rw [h]
  · exact A
  · exact B

theorem part4 (q : ℕ) (hq : 1 ≤ q) (o' : NeighborOrders (SimpleGraph.cycleGraph (q + 3))) :
    lambdaQ (SimpleGraph.cycleGraph (q + 3)) o' q +
          ENNReal.ofReal (Real.pi ^ 2 / (16 * ((q : ℝ) + 3) ^ 2)) ≤
        shearerThreshold (SimpleGraph.cycleGraph (q + 3)) := by
  have h := proposition_3_10 (q + 3) (by omega) o'
  have e : q + 3 - 3 = q := by omega
  have hq1 := (h.2.1 q hq (by omega))
  obtain ⟨hR, -, ⟨-, hdiff, hge⟩, -⟩ := h
  rw [shearer_eq _ o', hR]
  have hl : lambdaQ (SimpleGraph.cycleGraph (q + 3)) o' q = ENNReal.ofReal (1 / 4) := hq1
  rw [e] at hdiff hge
  rw [hl]
  rw [← ENNReal.ofReal_add (by norm_num) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hl' : (memRadius (indRep (SimpleGraph.cycleGraph (q + 3)) o') q).toReal = 1 / 4 := by
    show (lambdaQ _ o' q).toReal = _
    rw [hl, ENNReal.toReal_ofReal (by norm_num)]
  rw [hl', hR, ENNReal.toReal_ofReal (by positivity)] at hdiff
  push_cast at hdiff hge ⊢
  linarith

theorem part5 {V : Type} [Nonempty V] (G : SimpleGraph V) [G.LocallyFinite]
    (o : NeighborOrders G) (q : ℕ) (p : V → ℝ) (hp : ∀ v, 0 ≤ p v)
    (x : Hist (indRep G o) → ℝ) (hx : IsMemCertificate (indRep G o) q p x) (U : Finset V) :
    ZeroFreeOn (indepPoly G) U p ∧
        0 < MvPolynomial.eval (fun v => -p v) (indepPoly G U) := by
  classical
  have hrep := MZ.indep_rep G o
  have hz := (theorem_3_2 (indRep G o) (indepPoly G) hrep).1 q p hp x hx U
  refine ⟨hz, ?_⟩
  have := ((theorem_2_3 (indRep G o) (indepPoly G) hrep U p hp).1.mp hz) U (subset_refl _)
  exact this

end LocalLemmaHierarchy.Completeness.Dev.T11

namespace LocalLemmaHierarchy.Completeness

open LocalLemmaHierarchy.Completeness.Dev.T11 in
theorem chk_theorem_1_1 {V : Type} [Nonempty V] (G : SimpleGraph V) [G.LocallyFinite]
    (o : NeighborOrders G) :
    (Monotone (lambdaQ G o) ∧ (∀ q, lambdaQ G o q ≤ shearerThreshold G) ∧
      Tendsto (lambdaQ G o) atTop (𝓝 (shearerThreshold G))) ∧
    ((∀ p : V → ℝ, (∀ v, 0 ≤ p v) → ∀ x : Hist (indRep G o) → ℝ,
        (IsMemCertificate (indRep G o) 0 p x ↔
          ∀ v, 0 ≤ x (indState G o v) ∧ x (indState G o v) < 1 ∧
            p v ≤ x (indState G o v) * ∏ u ∈ G.neighborFinset v, (1 - x (indState G o u)))) ∧
      lambdaQ G o 0 =
        ⨆ (t : ℝ≥0) (_ : ∃ x : V → ℝ, ∀ v, 0 ≤ x v ∧ x v < 1 ∧
            (t : ℝ) ≤ x v * ∏ u ∈ G.neighborFinset v, (1 - x u)), (t : ℝ≥0∞)) ∧
    (∀ q : ℕ, 1 ≤ q →
      lambdaQ G o q ≤ shearerThreshold G ∧
      shearerThreshold G ≤
        lambdaQ G o q + ENNReal.ofReal (min (1 / (q : ℝ)) (Real.pi ^ 2 / ((q : ℝ) + 1) ^ 2))) ∧
    (∀ q : ℕ, 1 ≤ q → ∀ o' : NeighborOrders (SimpleGraph.cycleGraph (q + 3)),
      lambdaQ (SimpleGraph.cycleGraph (q + 3)) o' q +
          ENNReal.ofReal (Real.pi ^ 2 / (16 * ((q : ℝ) + 3) ^ 2)) ≤
        shearerThreshold (SimpleGraph.cycleGraph (q + 3))) ∧
    (∀ (q : ℕ) (p : V → ℝ), (∀ v, 0 ≤ p v) → ∀ x : Hist (indRep G o) → ℝ,
      IsMemCertificate (indRep G o) q p x → ∀ U : Finset V,
        ZeroFreeOn (indepPoly G) U p ∧
        0 < MvPolynomial.eval (fun v => -p v) (indepPoly G U)) :=
  ⟨part1 G o,
   ⟨fun p hp x => (memory_zero_lll G o p hp).1 x, part2b G o⟩,
   fun q hq => part3 G o q hq,
   fun q hq o' => part4 q hq o',
   fun q p hp x hx U => part5 G o q p hp x hx U⟩

end LocalLemmaHierarchy.Completeness
end

theorem solution : type_of% @LocalLemmaHierarchy.Completeness.chk_theorem_1_1 := @LocalLemmaHierarchy.Completeness.chk_theorem_1_1
