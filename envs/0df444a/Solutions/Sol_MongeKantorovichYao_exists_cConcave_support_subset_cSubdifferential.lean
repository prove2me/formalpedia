-- Prove2me | solution 1 for MongeKantorovichYao.exists_cConcave_support_subset_cSubdifferential
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T10:22:03.986871+00:00
-- url     : https://prove2.me/submissions/a06df67c-8e64-4c71-81b3-0b016fabb99a

/-
Released under Apache 2.0 license.
Written by Codex.
-/
import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs



open MeasureTheory Set Topology
namespace MongeKantorovichYao

lemma cyclic_closure {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    (c : X × Y → ℝ) (hc : Continuous c) (Γ : Set (X × Y))
    (hΓ : IsCCyclicallyMonotone c Γ) : IsCCyclicallyMonotone c (closure Γ) := by
  intro n p hp
  let A : Set (Fin (n+1) → X × Y) := Set.pi Set.univ (fun _ => Γ)
  let B : Set (Fin (n+1) → X × Y) :=
    {q | ∑ i, c (q i) ≤ ∑ i, c ((q i).1, (q (i+1)).2)}
  have hB : IsClosed B := by
    apply isClosed_le
    · exact continuous_finsetSum _ (fun i _ => hc.comp (continuous_apply i))
    · exact continuous_finsetSum _ (fun i _ =>
        hc.comp ((continuous_fst.comp (continuous_apply i)).prodMk
          (continuous_snd.comp (continuous_apply (i+1)))))
  have hAB : A ⊆ B := by
    intro q hq
    exact hΓ n q (fun i => hq i (Set.mem_univ i))
  exact (closure_minimal hAB hB) (mem_closure_pi.mpr (fun i _ => hp i))

lemma support_cyclic {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y]
    (c : X × Y → ℝ) (hc : Continuous c) (π : Measure (X × Y))
    (hπ : IsCCyclicallyMonotonePlan c π) : IsCCyclicallyMonotone c π.support := by
  obtain ⟨Γ, hΓ, hnull⟩ := hπ
  have hs : π.support ⊆ closure Γ := by
    apply π.support_subset_of_isClosed isClosed_closure
    show π (closure Γ)ᶜ = 0
    exact measure_mono_null (Set.compl_subset_compl.mpr subset_closure) hnull
  intro n p hp
  exact cyclic_closure c hc Γ hΓ n p (fun i => hs (hp i))

end MongeKantorovichYao


open MeasureTheory Set Topology
namespace MongeKantorovichYao

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

structure TransportChain (Γ : Set (X × Y)) (a : X × Y) where
  n : ℕ
  p : Fin (n+1) → X × Y
  mem : ∀ i, p i ∈ Γ
  anchor : p (Fin.last n) = a

namespace TransportChain

def base (Γ : Set (X × Y)) (a : X × Y) (ha : a ∈ Γ) : TransportChain Γ a :=
  ⟨0, fun _ => a, fun _ => ha, rfl⟩

def prepend {Γ : Set (X × Y)} {a : X × Y} (s : TransportChain Γ a)
    (q : X × Y) (hq : q ∈ Γ) : TransportChain Γ a where
  n := s.n+1
  p := Fin.cons q s.p
  mem := by intro i; refine Fin.cases hq (fun j => ?_) i; simpa using s.mem j
  anchor := by simpa using s.anchor

def cost {Γ : Set (X × Y)} {a : X × Y} (c : X × Y → ℝ)
    (s : TransportChain Γ a) (x : X) : ℝ :=
  c (x, (s.p 0).2) - c (s.p 0) +
    ∑ i : Fin s.n, (c ((s.p i.castSucc).1, (s.p i.succ).2) - c (s.p i.succ))

lemma cost_base (c : X × Y → ℝ) (Γ : Set (X × Y)) (a : X × Y) (ha : a ∈ Γ)
    (x : X) : (base Γ a ha).cost c x = c (x,a.2) - c a := by
  simp [cost, base]

lemma cost_prepend {Γ : Set (X × Y)} {a : X × Y} (c : X × Y → ℝ)
    (s : TransportChain Γ a) (q : X × Y) (hq : q ∈ Γ) (x : X) :
    (s.prepend q hq).cost c x = c (x,q.2) - c q + s.cost c q.1 := by
  dsimp only [cost, prepend]
  rw [Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero,
    Fin.cons_succ, Fin.castSucc_succ]

lemma cost_anchor_nonneg {Γ : Set (X × Y)} {a : X × Y} (c : X × Y → ℝ)
    (hΓ : IsCCyclicallyMonotone c Γ) (s : TransportChain Γ a) :
    0 ≤ s.cost c a.1 := by
  have h := hΓ s.n s.p s.mem
  have hidx (i : Fin s.n) : i.castSucc + 1 = i.succ := by
    apply Fin.ext
    exact Fin.val_add_one_of_lt (Fin.castSucc_lt_last i)
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at h
  simp only [hidx, Fin.last_add_one, s.anchor] at h
  simp only [cost, Finset.sum_sub_distrib]
  linarith

lemma cost_lower {Γ : Set (X × Y)} {a : X × Y} (c : X × Y → ℝ)
    (hΓ : IsCCyclicallyMonotone c Γ) (C : ℝ)
    (hc0 : ∀ p, 0 ≤ c p) (hcC : ∀ p, c p ≤ C)
    (s : TransportChain Γ a) (x : X) : -C ≤ s.cost c x := by
  have h := cost_anchor_nonneg c hΓ s
  have h0 := hc0 (x, (s.p 0).2)
  have hC := hcC (a.1, (s.p 0).2)
  simp only [cost] at h ⊢
  linarith

end TransportChain
end MongeKantorovichYao


open Set
namespace MongeKantorovichYao

noncomputable def realInf {ι : Type*} (f : ι → ℝ) : ℝ :=
  (⨅ i, (f i : EReal)).toReal

lemma realInf_coe {ι : Type*} [Nonempty ι] (f : ι → ℝ)
    (hb : BddBelow (Set.range f)) : (realInf f : EReal) = ⨅ i, (f i : EReal) := by
  obtain ⟨b,hb⟩ := hb
  have hl : (b : EReal) ≤ ⨅ i, (f i : EReal) :=
    le_iInf (fun i => EReal.coe_le_coe (hb (Set.mem_range_self i)))
  have hu : (⨅ i, (f i : EReal)) ≤ (f (Classical.arbitrary ι) : EReal) := iInf_le _ _
  apply EReal.coe_toReal
  · exact ne_of_lt (hu.trans_lt (EReal.coe_lt_top _))
  · exact ne_of_gt ((EReal.bot_lt_coe _).trans_le hl)

lemma realInf_le {ι : Type*} [Nonempty ι] (f : ι → ℝ)
    (hb : BddBelow (Set.range f)) (i : ι) : realInf f ≤ f i := by
  apply EReal.coe_le_coe_iff.mp
  rw [realInf_coe f hb]
  exact iInf_le _ i

lemma le_realInf {ι : Type*} [Nonempty ι] (f : ι → ℝ)
    (hb : BddBelow (Set.range f)) (b : ℝ) (h : ∀ i, b ≤ f i) : b ≤ realInf f := by
  apply EReal.coe_le_coe_iff.mp
  rw [realInf_coe f hb]
  exact le_iInf (fun i => EReal.coe_le_coe (h i))

end MongeKantorovichYao


open MeasureTheory Set Topology
namespace MongeKantorovichYao

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

noncomputable def chainPotential (c : X × Y → ℝ) (Γ : Set (X × Y)) (a : X × Y)
    (x : X) : ℝ := realInf (fun s : TransportChain Γ a => s.cost c x)

lemma bounded_potential_of_cyclic (c : X × Y → ℝ) (Γ : Set (X × Y))
    (hΓ : IsCCyclicallyMonotone c Γ) (a : X × Y) (ha : a ∈ Γ) (C : ℝ)
    (hc0 : ∀ p, 0 ≤ c p) (hcC : ∀ p, c p ≤ C) :
    IsCConcave c (chainPotential c Γ a) ∧
      Γ ⊆ cSubdifferential c (chainPotential c Γ a) ∧
      ∀ x, -C ≤ chainPotential c Γ a x ∧ chainPotential c Γ a x ≤ C := by
  classical
  letI : Nonempty (TransportChain Γ a) := ⟨TransportChain.base Γ a ha⟩
  letI : Nonempty X := ⟨a.1⟩
  letI : Nonempty Y := ⟨a.2⟩
  let ψ := chainPotential c Γ a
  have hb (x : X) : BddBelow (Set.range (fun s : TransportChain Γ a => s.cost c x)) := by
    refine ⟨-C, ?_⟩
    rintro z ⟨s, rfl⟩
    exact s.cost_lower c hΓ C hc0 hcC x
  have hψle (x : X) (s : TransportChain Γ a) : ψ x ≤ s.cost c x :=
    realInf_le _ (hb x) s
  have hleψ (x : X) (b : ℝ) (h : ∀ s : TransportChain Γ a, b ≤ s.cost c x) : b ≤ ψ x :=
    le_realInf _ (hb x) b h
  have hψcoe (x : X) : (ψ x : EReal) = ⨅ s : TransportChain Γ a, (s.cost c x : EReal) :=
    realInf_coe _ (hb x)
  have hψbounds (x : X) : -C ≤ ψ x ∧ ψ x ≤ C := by
    constructor
    · exact hleψ x (-C) (fun s => s.cost_lower c hΓ C hc0 hcC x)
    · have h := hψle x (TransportChain.base Γ a ha)
      rw [TransportChain.cost_base] at h
      have h0 := hc0 a
      have hu := hcC (x,a.2)
      linarith
  have hsupport (q : X × Y) (hq : q ∈ Γ) (x : X) :
      ψ x ≤ ψ q.1 + c (x,q.2) - c q := by
    have h := hleψ q.1 (ψ x - c (x,q.2) + c q) (fun s => by
      have hs := hψle x (s.prepend q hq)
      rw [TransportChain.cost_prepend] at hs
      linarith)
    linarith
  have hbφ (y : Y) : BddBelow (Set.range (fun x => c (x,y) - ψ x)) := by
    refine ⟨-C, ?_⟩
    rintro z ⟨x, rfl⟩
    have h0 := hc0 (x,y)
    have hu := (hψbounds x).2
    linarith
  let φ : Y → ℝ := fun y => realInf (fun x => c (x,y) - ψ x)
  have hφcoe (y : Y) : (φ y : EReal) = cConjugate c (fun x => (ψ x : EReal)) y := by
    dsimp only [φ, cConjugate]
    rw [realInf_coe _ (hbφ y)]
    simp only [EReal.coe_sub]
  have hφle (y : Y) (x : X) : φ y ≤ c (x,y) - ψ x :=
    realInf_le _ (hbφ y) x
  have hφsupport (q : X × Y) (hq : q ∈ Γ) : φ q.2 = c q - ψ q.1 := by
    apply le_antisymm
    · exact hφle q.2 q.1
    · apply le_realInf _ (hbφ q.2)
      intro x
      have h := hsupport q hq x
      linarith
  have hψdouble (x : X) : (ψ x : EReal) = cConjugate' c (fun y => (φ y : EReal)) x := by
    apply le_antisymm
    · apply le_iInf
      intro y
      rw [← EReal.coe_sub]
      apply EReal.coe_le_coe
      have h := hφle y x
      linarith
    · rw [hψcoe x]
      apply le_iInf
      intro s
      have h0 : cConjugate' c (fun y => (φ y : EReal)) x ≤
          (c (x,(s.p 0).2) - φ (s.p 0).2 : ℝ) := by
        convert (iInf_le (fun y =>
          (c (x,y) : EReal) - (φ y : EReal)) (s.p 0).2) using 1 <;> rfl
      apply h0.trans
      apply EReal.coe_le_coe
      rw [hφsupport (s.p 0) (s.mem 0)]
      have h := hψle (s.p 0).1 s
      have he : s.cost c x = s.cost c (s.p 0).1 +
          c (x,(s.p 0).2) - c (s.p 0) := by
        simp only [TransportChain.cost]
        ring
      rw [he]
      linarith
  refine ⟨⟨φ,hψdouble⟩, ?_, hψbounds⟩
  intro q hq
  change cConjugate c (fun x => (ψ x : EReal)) q.2 + (ψ q.1 : EReal) = (c q : EReal)
  rw [← hφcoe q.2, hφsupport q hq, ← EReal.coe_add]
  congr 1
  ring

end MongeKantorovichYao


open MeasureTheory
namespace MongeKantorovichYao

theorem potential_support {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (c : X × Y → ℝ) (hc_cont : Continuous c) (hc_nonneg : ∀ p, 0 ≤ c p)
    (hc_bdd : BddAbove (Set.range c))
    (π : Measure (X × Y)) [IsProbabilityMeasure π] (hπ : IsCCyclicallyMonotonePlan c π) :
    ∃ ψ : X → ℝ, IsCConcave c ψ ∧ π.support ⊆ cSubdifferential c ψ := by
  obtain ⟨a,ha⟩ := π.nonempty_support (IsProbabilityMeasure.ne_zero π)
  obtain ⟨C,hC⟩ := hc_bdd
  have hΓ := support_cyclic c hc_cont π hπ
  have hb := bounded_potential_of_cyclic c π.support hΓ a ha C hc_nonneg
    (fun p => hC (Set.mem_range_self p))
  exact ⟨chainPotential c π.support a, hb.1, hb.2.1⟩

end MongeKantorovichYao

open MongeKantorovichYao MeasureTheory
theorem solution {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (c : X × Y → ℝ) (hc_cont : Continuous c) (hc_nonneg : ∀ p, 0 ≤ c p)
    (hc_bdd : BddAbove (Set.range c))
    (π : Measure (X × Y)) [IsProbabilityMeasure π] (hπ : IsCCyclicallyMonotonePlan c π) :
    ∃ ψ : X → ℝ, IsCConcave c ψ ∧ π.support ⊆ cSubdifferential c ψ := by
  exact potential_support c hc_cont hc_nonneg hc_bdd π hπ

#print axioms solution
