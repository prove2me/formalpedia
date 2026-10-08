-- Prove2me | solution 1 for MongeKantorovichYao.duality_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T11:19:12.907994+00:00
-- url     : https://prove2.me/submissions/0f8cbee9-75a1-4dad-99b5-a5a278c6ee3d

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


open Set Finset Matrix
namespace MongeKantorovichYao
namespace Weighted

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def Couplings (a : I → ℝ) (b : J → ℝ) : Set (Matrix I J ℝ) :=
  {M | (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = a i) ∧ ∀ j, ∑ i, M i j = b j}

def cost (A M : Matrix I J ℝ) : ℝ := ∑ i, ∑ j, M i j * A i j

lemma coupling_nonempty (a : I → ℝ) (b : J → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (has : ∑ i, a i = 1) (hbs : ∑ j, b j = 1) : (Couplings a b).Nonempty := by
  refine ⟨fun i j => a i * b j, ?_⟩
  refine ⟨fun i j => mul_nonneg (ha i) (hb j), ?_, ?_⟩
  · intro i; simp only [← mul_sum, hbs, mul_one]
  · intro j; simp only [← sum_mul, has, one_mul]

lemma coupling_closed (a : I → ℝ) (b : J → ℝ) : IsClosed (Couplings a b) := by
  have h0 : IsClosed {M : Matrix I J ℝ | ∀ i j, 0 ≤ M i j} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    exact isClosed_le continuous_const (by fun_prop)
  have hr : IsClosed {M : Matrix I J ℝ | ∀ i, ∑ j, M i j = a i} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_eq (continuous_finsetSum _ (fun j _ => by fun_prop)) continuous_const
  have hc : IsClosed {M : Matrix I J ℝ | ∀ j, ∑ i, M i j = b j} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro j
    exact isClosed_eq (continuous_finsetSum _ (fun i _ => by fun_prop)) continuous_const
  exact h0.inter (hr.inter hc)

lemma coupling_compact (a : I → ℝ) (b : J → ℝ)
    (ha : ∀ i, 0 ≤ a i) (has : ∑ i, a i = 1) : IsCompact (Couplings a b) := by
  have hcomp : IsCompact (Set.pi Set.univ (fun _ : I =>
      Set.pi Set.univ (fun _ : J => Set.Icc (0 : ℝ) 1))) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  apply hcomp.of_isClosed_subset (coupling_closed a b)
  intro M hM i _ j _
  refine ⟨hM.1 i j, ?_⟩
  have hij : M i j ≤ a i := by
    rw [← hM.2.1 i]
    exact single_le_sum (fun k _ => hM.1 i k) (mem_univ j)
  have hi : a i ≤ 1 := by
    rw [← has]
    exact single_le_sum (fun k _ => ha k) (mem_univ i)
  exact hij.trans hi

lemma exists_min (A : Matrix I J ℝ) (a : I → ℝ) (b : J → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (has : ∑ i, a i = 1) (hbs : ∑ j, b j = 1) :
    ∃ M ∈ Couplings a b, ∀ N ∈ Couplings a b, cost A M ≤ cost A N := by
  have hcont : Continuous (cost A) := by
    unfold cost
    exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => by fun_prop))
  exact (coupling_compact a b ha has).exists_isMinOn
    (coupling_nonempty a b ha hb has hbs) hcont.continuousOn

end Weighted
end MongeKantorovichYao


open Finset Set Matrix
namespace MongeKantorovichYao.Weighted

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def cycleMatrix {K : Type*} [Fintype K] (r : K → I) (s : K → J) : Matrix I J ℝ :=
  fun i j => ∑ k, if r k = i ∧ s k = j then 1 else 0

lemma cycleMatrix_nonneg {K : Type*} [Fintype K] (r : K → I) (s : K → J) (i : I) (j : J) :
    0 ≤ cycleMatrix r s i j := by
  unfold cycleMatrix
  exact sum_nonneg (fun k _ => by split <;> norm_num)

lemma cycleMatrix_row {K : Type*} [Fintype K] (r : K → I) (s : K → J) (i : I) :
    ∑ j, cycleMatrix r s i j = ∑ k, if r k = i then (1 : ℝ) else 0 := by
  classical
  unfold cycleMatrix
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  by_cases h : r k = i
  · simp [h]
  · simp [h]

lemma cycleMatrix_col {K : Type*} [Fintype K] (r : K → I) (s : K → J) (j : J) :
    ∑ i, cycleMatrix r s i j = ∑ k, if s k = j then (1 : ℝ) else 0 := by
  classical
  unfold cycleMatrix
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  by_cases h : s k = j
  · simp [h]
  · simp [h]

lemma cycleMatrix_cost {K : Type*} [Fintype K] (A : Matrix I J ℝ) (r : K → I) (s : K → J) :
    cost A (cycleMatrix r s) = ∑ k, A (r k) (s k) := by
  classical
  unfold cost cycleMatrix
  simp_rw [sum_mul]
  calc
    (∑ i, ∑ j, ∑ k, (if r k = i ∧ s k = j then (1 : ℝ) else 0) * A i j) =
        ∑ i, ∑ k, ∑ j, (if r k = i ∧ s k = j then (1 : ℝ) else 0) * A i j := by
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = ∑ k, ∑ i, ∑ j, (if r k = i ∧ s k = j then (1 : ℝ) else 0) * A i j := by
      rw [sum_comm]
    _ = ∑ k, A (r k) (s k) := by
      apply sum_congr rfl
      intro k _
      simp [ite_and]


lemma cost_perturb (A M D B : Matrix I J ℝ) (ε : ℝ) :
    cost A (fun i j => M i j - ε * D i j + ε * B i j) =
      cost A M - ε * cost A D + ε * cost A B := by
  simp only [cost, add_mul, sub_mul, mul_assoc]
  simp_rw [sum_add_distrib, sum_sub_distrib, ← mul_sum]

lemma positive_support_cycle_inequality (A M : Matrix I J ℝ) (a : I → ℝ) (b : J → ℝ)
    (hM : M ∈ Couplings a b)
    (hmin : ∀ N ∈ Couplings a b, cost A M ≤ cost A N)
    {K : Type*} [Fintype K] [Nonempty K] (r : K → I) (s : K → J) (σ : Equiv.Perm K)
    (hpos : ∀ k, 0 < M (r k) (s k)) :
    ∑ k, A (r k) (s k) ≤ ∑ k, A (r k) (s (σ k)) := by
  classical
  obtain ⟨k0, _, hk0⟩ := Finset.exists_min_image Finset.univ
    (fun k => M (r k) (s k)) Finset.univ_nonempty
  let δ := M (r k0) (s k0)
  let L : ℝ := Fintype.card K
  have hL : 0 < L := by dsimp [L]; exact_mod_cast Fintype.card_pos
  have hδ : 0 < δ := hpos k0
  let ε := δ / L
  have hε : 0 < ε := div_pos hδ hL
  let D := cycleMatrix r s
  let B := cycleMatrix r (s ∘ σ)
  have hD (i : I) (j : J) : ε * D i j ≤ M i j := by
    have hterm (k : K) : δ * (if r k = i ∧ s k = j then (1 : ℝ) else 0) ≤ M i j := by
      by_cases h : r k = i ∧ s k = j
      · rw [if_pos h, mul_one]
        dsimp only [δ]
        simpa only [h.1, h.2] using hk0 k (Finset.mem_univ k)
      · simp only [h, ↓reduceIte, mul_zero]
        exact hM.1 i j
    have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hterm k)
    have hs : δ * D i j ≤ L * M i j := by
      simpa only [← mul_sum, D, cycleMatrix, sum_const, card_univ, nsmul_eq_mul, L] using hsum
    dsimp only [ε]
    rw [div_mul_eq_mul_div, div_le_iff₀ hL]
    simpa only [mul_comm] using hs
  have hrow (i : I) : ∑ j, D i j = ∑ j, B i j := by
    simp only [D, B, cycleMatrix_row]
  have hcol (j : J) : ∑ i, D i j = ∑ i, B i j := by
    simp only [D, B, cycleMatrix_col, Function.comp_apply]
    exact (Equiv.sum_comp σ (fun k => if s k = j then (1 : ℝ) else 0)).symm
  let N : Matrix I J ℝ := fun i j => M i j - ε * D i j + ε * B i j
  have hN : N ∈ Couplings a b := by
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      have hd := hD i j
      have hb := mul_nonneg hε.le (cycleMatrix_nonneg r (s ∘ σ) i j)
      dsimp [N]
      linarith
    · intro i
      dsimp only [N]
      simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, hrow i,
        hM.2.1]
      ring
    · intro j
      dsimp only [N]
      simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, hcol j,
        hM.2.2]
      ring
  have h := hmin N hN
  rw [cost_perturb] at h
  have heD : cost A D = ∑ k, A (r k) (s k) := cycleMatrix_cost A r s
  have heB : cost A B = ∑ k, A (r k) (s (σ k)) := cycleMatrix_cost A r (s ∘ σ)
  rw [heD, heB] at h
  nlinarith


end MongeKantorovichYao.Weighted


open MeasureTheory Finset Set Matrix
namespace MongeKantorovichYao.Weighted

variable {X Y I J : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

lemma row_ennreal (M : Matrix I J ℝ) (a : I → ℝ) (b : J → ℝ) (hM : M ∈ Couplings a b) (i : I) :
    ∑ j, ENNReal.ofReal (M i j) = ENNReal.ofReal (a i) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hM.1 _ _)]
  rw [hM.2.1]

lemma col_ennreal (M : Matrix I J ℝ) (a : I → ℝ) (b : J → ℝ) (hM : M ∈ Couplings a b) (j : J) :
    ∑ i, ENNReal.ofReal (M i j) = ENNReal.ofReal (b j) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hM.1 _ _)]
  rw [hM.2.2]

noncomputable def atomicTransport (x : I → X) (y : J → Y) (M : Matrix I J ℝ) : Measure (X × Y) :=
  ∑ i, ∑ j, ENNReal.ofReal (M i j) • Measure.dirac (x i, y j)

lemma atomicTransport_fst (x : I → X) (y : J → Y) (M : Matrix I J ℝ)
    (a : I → ℝ) (b : J → ℝ) (hM : M ∈ Couplings a b) :
    (atomicTransport x y M).map Prod.fst = ∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i) := by
  unfold atomicTransport
  rw [Measure.map_finset_sum measurable_fst.aemeasurable]
  apply sum_congr rfl
  intro i _
  rw [Measure.map_finset_sum measurable_fst.aemeasurable]
  simp only [Measure.map_smul, Measure.map_dirac, Prod.fst]
  rw [← Finset.sum_smul, row_ennreal M a b hM]

lemma atomicTransport_snd (x : I → X) (y : J → Y) (M : Matrix I J ℝ)
    (a : I → ℝ) (b : J → ℝ) (hM : M ∈ Couplings a b) :
    (atomicTransport x y M).map Prod.snd = ∑ j, ENNReal.ofReal (b j) • Measure.dirac (y j) := by
  have he : atomicTransport x y M =
      ∑ j, ∑ i, ENNReal.ofReal (M i j) • Measure.dirac (x i,y j) := by
    unfold atomicTransport
    rw [sum_comm]
  rw [he, Measure.map_finset_sum measurable_snd.aemeasurable]
  apply sum_congr rfl
  intro j _
  rw [Measure.map_finset_sum measurable_snd.aemeasurable]
  simp only [Measure.map_smul, Measure.map_dirac]
  rw [← Finset.sum_smul, col_ennreal M a b hM]

lemma atomicTransport_mass (x : I → X) (y : J → Y) (M : Matrix I J ℝ)
    (a : I → ℝ) (b : J → ℝ) (hM : M ∈ Couplings a b)
    (ha : ∀ i, 0 ≤ a i) (has : ∑ i, a i = 1) :
    atomicTransport x y M Set.univ = 1 := by
  simp only [atomicTransport, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one,
    row_ennreal M a b hM]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => ha i), has]
  norm_num

lemma atomicTransport_concentrated (x : I → X) (y : J → Y) (M : Matrix I J ℝ)
    (a : I → ℝ) (b : J → ℝ) (hM : M ∈ Couplings a b) :
    atomicTransport x y M {p | ∃ i j, 0 < M i j ∧ p = (x i,y j)}ᶜ = 0 := by
  unfold atomicTransport
  simp only [Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : 0 < M i j
  · have hp : (x i,y j) ∈ {p | ∃ i j, 0 < M i j ∧ p = (x i,y j)} := ⟨i,j,hij,rfl⟩
    simp [Measure.smul_apply, Measure.dirac_apply, Set.indicator_of_notMem,
      Set.notMem_compl_iff.mpr hp]
  · have hz : M i j = 0 := le_antisymm (le_of_not_gt hij) (hM.1 _ _)
    simp [hz]


lemma finite_weighted_plan (x : I → X) (y : J → Y) (a : I → ℝ) (b : J → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (has : ∑ i, a i = 1) (hbs : ∑ j, b j = 1) (c : X × Y → ℝ) :
    ∃ π ∈ transferencePlans (∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i))
      (∑ j, ENNReal.ofReal (b j) • Measure.dirac (y j)),
      IsCCyclicallyMonotonePlan c π := by
  classical
  let A : Matrix I J ℝ := fun i j => c (x i,y j)
  obtain ⟨M,hM,hmin⟩ := exists_min A a b ha hb has hbs
  let π := atomicTransport x y M
  have hprob : IsProbabilityMeasure π := ⟨atomicTransport_mass x y M a b hM ha has⟩
  have hfst := atomicTransport_fst x y M a b hM
  have hsnd := atomicTransport_snd x y M a b hM
  let Γ : Set (X × Y) := {p | ∃ i j, 0 < M i j ∧ p = (x i,y j)}
  have hΓ : IsCCyclicallyMonotone c Γ := by
    intro N p hp
    choose r s hpos he using hp
    have h := positive_support_cycle_inequality A M a b hM hmin r s
      (Equiv.addRight (1 : Fin (N+1))) hpos
    have hpEq : p = fun k => (x (r k),y (s k)) := funext he
    rw [hpEq]
    convert h using 1 <;> rfl
  have hnull := atomicTransport_concentrated x y M a b hM
  exact ⟨π, ⟨hprob,hfst,hsnd⟩, Γ,hΓ,hnull⟩

end MongeKantorovichYao.Weighted


open MeasureTheory Filter Set Topology Finset
namespace MongeKantorovichYao

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

noncomputable def simpleWeights (μ : ProbabilityMeasure X) (f : SimpleFunc X X)
    (i : f.range) : ℝ := ((μ : Measure X) (f ⁻¹' {i.1})).toReal

lemma simpleWeights_nonneg (μ : ProbabilityMeasure X) (f : SimpleFunc X X) (i : f.range) :
    0 ≤ simpleWeights μ f i := ENNReal.toReal_nonneg

lemma simpleWeights_sum (μ : ProbabilityMeasure X) (f : SimpleFunc X X) :
    ∑ i : f.range, simpleWeights μ f i = 1 := by
  classical
  have hsum : (∑ i ∈ f.range, (μ : Measure X) (f ⁻¹' {i})) = 1 := by
    rw [sum_measure_preimage_singleton]
    · have hpre : f ⁻¹' (↑f.range : Set X) = Set.univ := by
        ext x
        simp only [Set.mem_preimage, Finset.mem_coe, Set.mem_univ, iff_true]
        exact f.mem_range_self x
      rw [hpre, measure_univ]
    · intro i _
      exact f.measurable (measurableSet_singleton i)
  simp only [simpleWeights]
  rw [Finset.sum_coe_sort f.range (fun i => ((μ : Measure X) (f ⁻¹' {i})).toReal),
    ← ENNReal.toReal_sum (fun i _ => measure_ne_top _ _), hsum]
  norm_num

lemma simple_map_eq_atoms (μ : ProbabilityMeasure X) (f : SimpleFunc X X) :
    (μ.map f.measurable.aemeasurable : Measure X) =
      ∑ i : f.range, ENNReal.ofReal (simpleWeights μ f i) • Measure.dirac (i.1) := by
  classical
  change (μ : Measure X).map f = _
  have he := (Measure.ae_mem_finset_iff_map_eq_sum_dirac (s := f.range) (μ := (μ : Measure X))
    f.measurable.aemeasurable).mp (Filter.Eventually.of_forall (fun x => f.mem_range_self x))
  rw [he]
  simp only [simpleWeights]
  rw [Finset.sum_coe_sort f.range (fun i =>
    ENNReal.ofReal ((μ : Measure X) (f ⁻¹' {i})).toReal • Measure.dirac i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]

end MongeKantorovichYao


open MeasureTheory Filter Set Topology TopologicalSpace
namespace MongeKantorovichYao

lemma simple_map_tendsto {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : ProbabilityMeasure X) (f : ℕ → SimpleFunc X X)
    (hf : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 x)) :
    Tendsto (fun n => μ.map (f n).measurable.aemeasurable) atTop (𝓝 μ) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro g
  have hm (n : ℕ) : AEStronglyMeasurable (fun x => g (f n x)) (μ : Measure X) :=
    (g.continuous.measurable.comp (f n).measurable).aestronglyMeasurable
  have hd := tendsto_integral_of_dominated_convergence (μ := (μ : Measure X))
    (fun _ => ‖g‖) hm (integrable_const ‖g‖)
    (fun n => Filter.Eventually.of_forall (fun x => g.norm_coe_le_norm (f n x)))
    (Filter.Eventually.of_forall (fun x => g.continuous.continuousAt.tendsto.comp (hf x)))
  convert hd using 1
  funext n
  exact integral_map_of_stronglyMeasurable (f n).measurable g.continuous.stronglyMeasurable

lemma exists_simple_map_tendsto {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [SeparableSpace X] (μ : ProbabilityMeasure X) :
    ∃ f : ℕ → SimpleFunc X X,
      Tendsto (fun n => μ.map (f n).measurable.aemeasurable) atTop (𝓝 μ) := by
  classical
  letI : Nonempty X := nonempty_of_isProbabilityMeasure (μ : Measure X)
  let x0 : X := Classical.arbitrary X
  let f : ℕ → SimpleFunc X X := SimpleFunc.approxOn id measurable_id Set.univ x0 (Set.mem_univ x0)
  refine ⟨f, simple_map_tendsto μ f ?_⟩
  intro x
  exact SimpleFunc.tendsto_approxOn measurable_id (Set.mem_univ x0) (by simp)

end MongeKantorovichYao


open MeasureTheory Filter Set Topology TopologicalSpace
namespace MongeKantorovichYao

lemma cyclic_plan_tendsto {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (c : X × Y → ℝ) (hc : Continuous c)
    (πs : ℕ → ProbabilityMeasure (X × Y)) (π : ProbabilityMeasure (X × Y))
    (hlim : Tendsto πs atTop (𝓝 π))
    (hcyc : ∀ n, IsCCyclicallyMonotonePlan c (πs n : Measure (X × Y))) :
    IsCCyclicallyMonotonePlan c (π : Measure (X × Y)) := by
  classical
  letI := upgradeIsCompletelyMetrizable X
  letI := upgradeIsCompletelyMetrizable Y
  have hs (n : ℕ) : IsCCyclicallyMonotone c (πs n : Measure (X × Y)).support :=
    support_cyclic c hc (πs n : Measure (X × Y)) (hcyc n)
  refine ⟨(π : Measure (X × Y)).support, ?_, Measure.measure_compl_support⟩
  intro N p hp
  by_contra! hbad
  let V : Set (Fin (N+1) → X × Y) :=
    {q | ∑ i, c ((q i).1,(q (i+1)).2) < ∑ i, c (q i)}
  have hV : IsOpen V := by
    apply isOpen_lt
    · exact continuous_finsetSum _ (fun i _ =>
        hc.comp ((continuous_fst.comp (continuous_apply i)).prodMk
          (continuous_snd.comp (continuous_apply (i+1)))))
    · exact continuous_finsetSum _ (fun i _ => hc.comp (continuous_apply i))
  obtain ⟨F,U,hU,hsub⟩ := isOpen_pi_iff.mp hV p hbad
  let W : Fin (N+1) → Set (X × Y) := fun i => if i ∈ F then U i else Set.univ
  have hw (i : Fin (N+1)) : IsOpen (W i) ∧ p i ∈ W i := by
    by_cases hi : i ∈ F
    · simpa only [W, hi, ↓reduceIte] using hU i hi
    · simp [W,hi]
  have he (i : Fin (N+1)) : ∀ᶠ n in atTop, 0 < (πs n : Measure (X × Y)) (W i) := by
    have hpos : 0 < (π : Measure (X × Y)) (W i) :=
      (Measure.mem_support_iff_forall (p i)).mp (hp i) (W i) ((hw i).1.mem_nhds (hw i).2)
    have hli := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim (hw i).1
    exact eventually_lt_of_lt_liminf (hpos.trans_le hli)
  obtain ⟨n,hn⟩ := (Filter.eventually_all.mpr he).exists
  have hq (i : Fin (N+1)) : ∃ q ∈ W i, q ∈ (πs n : Measure (X × Y)).support :=
    (πs n : Measure (X × Y)).nonempty_inter_support_of_pos (hn i)
  choose q hqW hqS using hq
  have hqV : q ∈ V := hsub (fun i hi => by
    have hi' : i ∈ F := hi
    simpa only [W, hi', ↓reduceIte] using hqW i)
  have hqC := hs n N q hqS
  exact (not_lt_of_ge hqC) hqV

end MongeKantorovichYao


open MeasureTheory Filter Set Topology TopologicalSpace
namespace MongeKantorovichYao

lemma tight_range_of_tendsto {X : Type*} [MetricSpace X] [CompleteSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hlim : Tendsto μs atTop (𝓝 μ)) :
    IsTightMeasureSet (Set.range (fun n => (μs n : Measure X))) := by
  have hK : IsCompact (closure (Set.range μs)) :=
    hlim.isCompact_insert_range.closure_of_subset (Set.subset_insert μ (Set.range μs))
  apply (isTightMeasureSet_of_isCompact_closure hK).subset
  rintro ρ ⟨n,rfl⟩
  exact ⟨μs n, Set.mem_range_self n, rfl⟩

lemma limit_cyclic_couplings {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (c : X × Y → ℝ) (hc : Continuous c)
    (μs : ℕ → ProbabilityMeasure X) (νs : ℕ → ProbabilityMeasure Y)
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (πs : ℕ → ProbabilityMeasure (X × Y))
    (hfst : ∀ n, (πs n : Measure (X × Y)).map Prod.fst = (μs n : Measure X))
    (hsnd : ∀ n, (πs n : Measure (X × Y)).map Prod.snd = (νs n : Measure Y))
    (hcyc : ∀ n, IsCCyclicallyMonotonePlan c (πs n : Measure (X × Y))) :
    ∃ π ∈ transferencePlans (μ : Measure X) (ν : Measure Y), IsCCyclicallyMonotonePlan c π := by
  classical
  letI := upgradeIsCompletelyMetrizable X
  letI := upgradeIsCompletelyMetrizable Y
  have hμt := tight_range_of_tendsto μs μ hμ
  have hνt := tight_range_of_tendsto νs ν hν
  have hπt : IsTightMeasureSet (Set.range (fun n => (πs n : Measure (X × Y)))) := by
    apply IsTightMeasureSet.prodMk
    · apply hμt.subset
      rintro ρ ⟨π',⟨n,rfl⟩,rfl⟩
      exact ⟨n, (hfst n).symm⟩
    · apply hνt.subset
      rintro ρ ⟨π',⟨n,rfl⟩,rfl⟩
      exact ⟨n, (hsnd n).symm⟩
  have hπt' : IsTightMeasureSet {((ρ : ProbabilityMeasure (X × Y)) : Measure (X × Y)) |
      ρ ∈ Set.range πs} := by
    apply hπt.subset
    rintro ρ ⟨ρ',⟨n,rfl⟩,rfl⟩
    exact Set.mem_range_self n
  have hK := isCompact_closure_of_isTightMeasureSet hπt'
  obtain ⟨π,_,φ,hφ,hlim⟩ := hK.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  have heF (n : ℕ) : (πs n).map measurable_fst.aemeasurable = μs n :=
    Subtype.ext (hfst n)
  have heS (n : ℕ) : (πs n).map measurable_snd.aemeasurable = νs n :=
    Subtype.ext (hsnd n)
  have hpF : π.map measurable_fst.aemeasurable = μ := by
    apply tendsto_nhds_unique ?_ (hμ.comp hφ.tendsto_atTop)
    have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous (πs ∘ φ) π hlim continuous_fst
    simpa only [Function.comp_def, heF] using h
  have hpS : π.map measurable_snd.aemeasurable = ν := by
    apply tendsto_nhds_unique ?_ (hν.comp hφ.tendsto_atTop)
    have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous (πs ∘ φ) π hlim continuous_snd
    simpa only [Function.comp_def, heS] using h
  have hpC := cyclic_plan_tendsto c hc (πs ∘ φ) π hlim (fun n => hcyc (φ n))
  exact ⟨(π : Measure (X × Y)), ⟨inferInstance, congrArg Subtype.val hpF,
    congrArg Subtype.val hpS⟩, hpC⟩

end MongeKantorovichYao


open MeasureTheory Filter Set Topology TopologicalSpace
namespace MongeKantorovichYao

lemma simple_coupling_exists {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (f : SimpleFunc X X) (g : SimpleFunc Y Y) (c : X × Y → ℝ) :
    ∃ π ∈ transferencePlans (μ.map f.measurable.aemeasurable : Measure X)
      (ν.map g.measurable.aemeasurable : Measure Y), IsCCyclicallyMonotonePlan c π := by
  classical
  rw [simple_map_eq_atoms μ f, simple_map_eq_atoms ν g]
  exact Weighted.finite_weighted_plan (fun i : f.range => (i : X)) (fun j : g.range => (j : Y))
    (simpleWeights μ f) (simpleWeights ν g) (simpleWeights_nonneg μ f)
    (simpleWeights_nonneg ν g) (simpleWeights_sum μ f) (simpleWeights_sum ν g) c

lemma general_cyclic_plan {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : X × Y → ℝ) (hc_cont : Continuous c) (hc_nonneg : ∀ p, 0 ≤ c p) :
    ∃ π ∈ transferencePlans μ ν, IsCCyclicallyMonotonePlan c π := by
  classical
  letI := upgradeIsCompletelyMetrizable X
  letI := upgradeIsCompletelyMetrizable Y
  let μp : ProbabilityMeasure X := ⟨μ, inferInstance⟩
  let νp : ProbabilityMeasure Y := ⟨ν, inferInstance⟩
  obtain ⟨f,hf⟩ := exists_simple_map_tendsto μp
  obtain ⟨g,hg⟩ := exists_simple_map_tendsto νp
  let μs : ℕ → ProbabilityMeasure X := fun n => μp.map (f n).measurable.aemeasurable
  let νs : ℕ → ProbabilityMeasure Y := fun n => νp.map (g n).measurable.aemeasurable
  have hx (n : ℕ) : ∃ π ∈ transferencePlans (μs n : Measure X) (νs n : Measure Y),
      IsCCyclicallyMonotonePlan c π := simple_coupling_exists μp νp (f n) (g n) c
  choose ρ hρ hρC using hx
  let πs : ℕ → ProbabilityMeasure (X × Y) := fun n => ⟨ρ n, (hρ n).1⟩
  exact limit_cyclic_couplings c hc_cont μs νs μp νp hf hg πs
    (fun n => (hρ n).2.1) (fun n => (hρ n).2.2) hρC

end MongeKantorovichYao


open Set MeasureTheory Topology
namespace MongeKantorovichYao

lemma realInf_lt_iff {ι : Type*} [Nonempty ι] (f : ι → ℝ)
    (hb : BddBelow (range f)) (r : ℝ) : realInf f < r ↔ ∃ i, f i < r := by
  rw [← EReal.coe_lt_coe_iff, realInf_coe f hb, iInf_lt_iff]
  simp only [EReal.coe_lt_coe_iff]

lemma realInf_upperSemicontinuous {Z ι : Type*} [TopologicalSpace Z] [Nonempty ι]
    (f : ι → Z → ℝ) (hf : ∀ i, Continuous (f i))
    (hb : ∀ z, BddBelow (range (fun i => f i z))) :
    UpperSemicontinuous (fun z => realInf (fun i => f i z)) := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro r
  have he : (fun z => realInf (fun i => f i z)) ⁻¹' Iio r =
      ⋃ i, (f i) ⁻¹' Iio r := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion]
    exact realInf_lt_iff _ (hb z) r
  rw [he]
  exact isOpen_iUnion (fun i => isOpen_Iio.preimage (hf i))

lemma compact_cutoff {Z : Type*} [TopologicalSpace Z] [NormalSpace Z] [T2Space Z]
    (K U : Set Z) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ a : BoundedContinuousFunction Z ℝ,
      (∀ z, 0 ≤ a z ∧ a z ≤ 1) ∧ (∀ z ∈ K, a z = 1) ∧
      (∀ z ∉ U, a z = 0) := by
  obtain ⟨a,ha0,ha1,ha⟩ := exists_continuous_zero_one_of_isClosed
    hU.isClosed_compl hK.isClosed (by
      rw [Set.disjoint_left]
      intro z hzU hzK
      exact hzU (hKU hzK))
  let a' := BoundedContinuousFunction.ofNormedAddCommGroup a a.continuous 1 (fun z => by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [(ha z).1], (ha z).2⟩)
  exact ⟨a', ha, ha1, ha0⟩

lemma bcf_inf_apply {Z I : Type*} [TopologicalSpace Z] (t : Finset I) (ht : t.Nonempty)
    (F : I → BoundedContinuousFunction Z ℝ) (z : Z) :
    (t.inf' ht F) z = t.inf' ht (fun i => F i z) := by
  exact Finset.apply_inf'_eq_inf'_comp ht (fun f : BoundedContinuousFunction Z ℝ => f z)
    (fun _ _ => rfl)

lemma compact_envelopes {X Y I J : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Nonempty I] [Nonempty J]
    (c : X × Y → ℝ) (hc : Continuous c) (ψ : X → ℝ) (φ : Y → ℝ)
    (hfeas : ∀ x y, ψ x + φ y ≤ c (x,y))
    (F : I → BoundedContinuousFunction X ℝ) (G : J → BoundedContinuousFunction Y ℝ)
    (D : ℝ) (hFlo : ∀ i x, -D ≤ F i x) (hFhi : ∀ i x, F i x ≤ D)
    (hGlo : ∀ j y, -D ≤ G j y) (hGhi : ∀ j y, G j y ≤ D)
    (hψF : ∀ i x, ψ x ≤ F i x) (hφG : ∀ j y, φ y ≤ G j y)
    (hFapprox : ∀ x ε, 0 < ε → ∃ i, F i x < ψ x + ε)
    (hGapprox : ∀ y ε, 0 < ε → ∃ j, G j y < φ y + ε)
    (K : Set X) (L : Set Y) (hK : IsCompact K) (hL : IsCompact L)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : BoundedContinuousFunction X ℝ, ∃ g : BoundedContinuousFunction Y ℝ,
      (∀ x, -D ≤ f x ∧ f x ≤ D ∧ ψ x ≤ f x) ∧
      (∀ y, -D ≤ g y ∧ g y ≤ D ∧ φ y ≤ g y) ∧
      ∀ x ∈ K, ∀ y ∈ L, f x + g y < c (x,y) + ε := by
  classical
  let U : I × J → Set (X × Y) := fun ij =>
    {p | F ij.1 p.1 + G ij.2 p.2 < c p + ε}
  have hU (ij : I × J) : IsOpen (U ij) :=
    isOpen_lt ((F ij.1).continuous.comp continuous_fst |>.add
      ((G ij.2).continuous.comp continuous_snd)) (hc.add continuous_const)
  have hcover : K ×ˢ L ⊆ ⋃ ij, U ij := by
    intro p hp
    obtain ⟨i,hi⟩ := hFapprox p.1 (ε/2) (by positivity)
    obtain ⟨j,hj⟩ := hGapprox p.2 (ε/2) (by positivity)
    refine mem_iUnion.mpr ⟨(i,j), ?_⟩
    change F i p.1 + G j p.2 < c p + ε
    have h := hfeas p.1 p.2
    linarith
  obtain ⟨t,ht⟩ := (hK.prod hL).elim_finite_subcover U hU hcover
  let t' := insert (Classical.arbitrary I, Classical.arbitrary J) t
  have htn : t'.Nonempty := Finset.insert_nonempty _ _
  let f := t'.inf' htn (fun ij => F ij.1)
  let g := t'.inf' htn (fun ij => G ij.2)
  have hfle (ij : I × J) (hij : ij ∈ t') (x : X) : f x ≤ F ij.1 x :=
    Finset.inf'_le (fun ij => F ij.1) hij x
  have hgle (ij : I × J) (hij : ij ∈ t') (y : Y) : g y ≤ G ij.2 y :=
    Finset.inf'_le (fun ij => G ij.2) hij y
  refine ⟨f,g,?_,?_,?_⟩
  · intro x
    refine ⟨?_, ?_, ?_⟩
    · have h : BoundedContinuousFunction.const X (-D) ≤ f :=
        Finset.le_inf' htn (fun ij => F ij.1) (fun ij _ x => hFlo ij.1 x)
      exact h x
    · exact (hfle _ (Finset.mem_insert_self _ _) x).trans (hFhi _ x)
    · dsimp only [f]
      rw [bcf_inf_apply]
      exact Finset.le_inf' htn _ (fun ij _ => hψF ij.1 x)
  · intro y
    refine ⟨?_, ?_, ?_⟩
    · have h : BoundedContinuousFunction.const Y (-D) ≤ g :=
        Finset.le_inf' htn (fun ij => G ij.2) (fun ij _ y => hGlo ij.2 y)
      exact h y
    · exact (hgle _ (Finset.mem_insert_self _ _) y).trans (hGhi _ y)
    · dsimp only [g]
      rw [bcf_inf_apply]
      exact Finset.le_inf' htn _ (fun ij _ => hφG ij.2 y)
  · intro x hx y hy
    obtain ⟨ij,hijt,hij⟩ := mem_iUnion₂.mp (ht (show (x,y) ∈ K ×ˢ L from ⟨hx,hy⟩))
    have hi : ij ∈ t' := Finset.mem_insert_of_mem hijt
    exact lt_of_le_of_lt (add_le_add (hfle ij hi x) (hgle ij hi y)) hij

lemma continuous_feasible_on_compacts {X Y I J : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [NormalSpace X] [NormalSpace Y]
    [T2Space X] [T2Space Y] [Nonempty I] [Nonempty J]
    (c : X × Y → ℝ) (hc : Continuous c) (hc0 : ∀ p, 0 ≤ c p)
    (ψ : X → ℝ) (φ : Y → ℝ) (hfeas : ∀ x y, ψ x + φ y ≤ c (x,y))
    (F : I → BoundedContinuousFunction X ℝ) (G : J → BoundedContinuousFunction Y ℝ)
    (D : ℝ) (hD : 0 ≤ D)
    (hFlo : ∀ i x, -D ≤ F i x) (hFhi : ∀ i x, F i x ≤ D)
    (hGlo : ∀ j y, -D ≤ G j y) (hGhi : ∀ j y, G j y ≤ D)
    (hψF : ∀ i x, ψ x ≤ F i x) (hφG : ∀ j y, φ y ≤ G j y)
    (hFapprox : ∀ x ε, 0 < ε → ∃ i, F i x < ψ x + ε)
    (hGapprox : ∀ y ε, 0 < ε → ∃ j, G j y < φ y + ε)
    (K : Set X) (L : Set Y) (hK : IsCompact K) (hL : IsCompact L)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : BoundedContinuousFunction X ℝ, ∃ g : BoundedContinuousFunction Y ℝ,
      (∀ x y, f x + g y ≤ c (x,y)) ∧
      (∀ x, ψ x ≤ f x + Kᶜ.indicator (fun _ => 2*D) x) ∧
      (∀ y, φ y ≤ g y + ε + Lᶜ.indicator (fun _ => 2*D) y) := by
  classical
  obtain ⟨f,g,hf,hg,hfg⟩ := compact_envelopes c hc ψ φ hfeas F G D
    hFlo hFhi hGlo hGhi hψF hφG hFapprox hGapprox K L hK hL (ε/2) (by positivity)
  let N : Set (X × Y) := {p | f p.1 + g p.2 < c p + ε}
  have hN : IsOpen N := isOpen_lt
    ((f.continuous.comp continuous_fst).add (g.continuous.comp continuous_snd))
    (hc.add continuous_const)
  have hKL : K ×ˢ L ⊆ N := by
    intro p hp
    have h := hfg p.1 hp.1 p.2 hp.2
    change f p.1 + g p.2 < c p + ε
    linarith
  obtain ⟨U,V,hU,hV,hKU,hLV,hUV⟩ := generalized_tube_lemma hK hL hN hKL
  obtain ⟨a,ha,haK,haU⟩ := compact_cutoff K U hK hU hKU
  obtain ⟨b,hb,hbL,hbV⟩ := compact_cutoff L V hL hV hLV
  let f' := a * f + (1-a) * BoundedContinuousFunction.const X (-D)
  let g' := b * g + (1-b) * BoundedContinuousFunction.const Y (-D) -
    BoundedContinuousFunction.const Y ε
  have hf' (x : X) : -D ≤ f' x ∧ f' x ≤ f x := by
    change -D ≤ a x * f x + (1-a x)*(-D) ∧ a x*f x+(1-a x)*(-D) ≤ f x
    have h1 := mul_nonneg (ha x).1 (by linarith [(hf x).1] : 0 ≤ f x + D)
    have h2 := mul_nonneg (by linarith [(ha x).2] : 0 ≤ 1-a x)
      (by linarith [(hf x).1] : 0 ≤ f x + D)
    constructor <;> nlinarith
  have hg' (y : Y) : -D-ε ≤ g' y ∧ g' y ≤ g y-ε := by
    change -D-ε ≤ b y*g y+(1-b y)*(-D)-ε ∧
      b y*g y+(1-b y)*(-D)-ε ≤ g y-ε
    have h1 := mul_nonneg (hb y).1 (by linarith [(hg y).1] : 0 ≤ g y+D)
    have h2 := mul_nonneg (by linarith [(hb y).2] : 0 ≤ 1-b y)
      (by linarith [(hg y).1] : 0 ≤ g y+D)
    constructor <;> nlinarith
  refine ⟨f',g',?_,?_,?_⟩
  · intro x y
    by_cases hx : x ∈ U
    · by_cases hy : y ∈ V
      · have h := hUV (show (x,y) ∈ U ×ˢ V from ⟨hx,hy⟩)
        change f x+g y < c (x,y)+ε at h
        linarith [(hf' x).2,(hg' y).2]
      · have he : g' y = -D-ε := by
          change b y*g y+(1-b y)*(-D)-ε = -D-ε
          rw [hbV y hy]
          ring
        rw [he]
        linarith [(hf' x).2,(hf x).2.1,hc0 (x,y)]
    · have he : f' x = -D := by
        change a x*f x+(1-a x)*(-D) = -D
        rw [haU x hx]
        ring
      rw [he]
      linarith [(hg' y).2,(hg y).2.1,hc0 (x,y)]
  · intro x
    by_cases hx : x ∈ K
    · rw [indicator_of_notMem (by simpa using hx : x ∉ Kᶜ)]
      have he : f' x = f x := by
        change a x*f x+(1-a x)*(-D) = f x
        rw [haK x hx]
        ring
      rw [he,add_zero]
      exact (hf x).2.2
    · rw [indicator_of_mem (show x ∈ Kᶜ from hx)]
      linarith [(hf' x).1,(hf x).2.1,(hf x).2.2]
  · intro y
    by_cases hy : y ∈ L
    · rw [indicator_of_notMem (by simpa using hy : y ∉ Lᶜ)]
      have he : g' y = g y-ε := by
        change b y*g y+(1-b y)*(-D)-ε = g y-ε
        rw [hbL y hy]
        ring
      rw [he,add_zero]
      linarith [(hg y).2.2]
    · rw [indicator_of_mem (show y ∈ Lᶜ from hy)]
      linarith [(hg' y).1,(hg y).2.1,(hg y).2.2]

end MongeKantorovichYao


open Set MeasureTheory Topology
namespace MongeKantorovichYao

variable {Z : Type*} [TopologicalSpace Z]

def HasContinuousEnvelopes (f : Z → ℝ) (D : ℝ) : Prop :=
  ∀ z ε, 0 < ε → ∃ F : BoundedContinuousFunction Z ℝ,
    (∀ w, -D ≤ F w ∧ F w ≤ D ∧ f w ≤ F w) ∧ F z < f z + ε

lemma realInf_envelopes {I : Type*} [Nonempty I] (f : I → Z → ℝ)
    (hf : ∀ i, Continuous (f i)) (D : ℝ) (hD : 0 ≤ D)
    (hlo : ∀ i z, -D ≤ f i z)
    (hhi : ∀ z, realInf (fun i => f i z) ≤ D) :
    HasContinuousEnvelopes (fun z => realInf (fun i => f i z)) D := by
  classical
  have hb (z : Z) : BddBelow (range (fun i => f i z)) :=
    ⟨-D, by rintro _ ⟨i,rfl⟩; exact hlo i z⟩
  intro z ε hε
  obtain ⟨i,hi⟩ := (realInf_lt_iff _ (hb z) (realInf (fun i => f i z)+ε)).mp (by linarith)
  let F := BoundedContinuousFunction.ofNormedAddCommGroup (fun w => min D (f i w))
    (continuous_const.min (hf i)) D (fun w => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨le_min (by linarith) (hlo i w), min_le_left _ _⟩)
  refine ⟨F,?_,?_⟩
  · intro w
    change -D ≤ min D (f i w) ∧ min D (f i w) ≤ D ∧
      realInf (fun i => f i w) ≤ min D (f i w)
    exact ⟨le_min (by linarith) (hlo i w),min_le_left _ _,
      le_min (hhi w) (realInf_le _ (hb w) i)⟩
  · exact (min_le_right _ _).trans_lt hi

lemma continuous_feasible_from_envelopes {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [NormalSpace X] [NormalSpace Y]
    [T2Space X] [T2Space Y] [Nonempty X] [Nonempty Y]
    (c : X × Y → ℝ) (hc : Continuous c) (hc0 : ∀ p, 0 ≤ c p)
    (ψ : X → ℝ) (φ : Y → ℝ) (hfeas : ∀ x y, ψ x+φ y ≤ c (x,y))
    (D : ℝ) (hD : 0 ≤ D) (hF : HasContinuousEnvelopes ψ D)
    (hG : HasContinuousEnvelopes φ D)
    (K : Set X) (L : Set Y) (hK : IsCompact K) (hL : IsCompact L)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : BoundedContinuousFunction X ℝ, ∃ g : BoundedContinuousFunction Y ℝ,
      (∀ x y, f x+g y ≤ c (x,y)) ∧
      (∀ x, ψ x ≤ f x+Kᶜ.indicator (fun _ => 2*D) x) ∧
      (∀ y, φ y ≤ g y+ε+Lᶜ.indicator (fun _ => 2*D) y) := by
  classical
  let I := {F : BoundedContinuousFunction X ℝ // ∀ x, -D ≤ F x ∧ F x ≤ D ∧ ψ x ≤ F x}
  let J := {G : BoundedContinuousFunction Y ℝ // ∀ y, -D ≤ G y ∧ G y ≤ D ∧ φ y ≤ G y}
  have hI : Nonempty I := by
    obtain ⟨f,hf,_⟩ := hF (Classical.arbitrary X) 1 zero_lt_one
    exact ⟨⟨f,hf⟩⟩
  have hJ : Nonempty J := by
    obtain ⟨g,hg,_⟩ := hG (Classical.arbitrary Y) 1 zero_lt_one
    exact ⟨⟨g,hg⟩⟩
  letI := hI
  letI := hJ
  exact continuous_feasible_on_compacts c hc hc0 ψ φ hfeas
    (fun i : I => i.val) (fun j : J => j.val) D hD
    (fun i x => (i.property x).1) (fun i x => (i.property x).2.1)
    (fun j y => (j.property y).1) (fun j y => (j.property y).2.1)
    (fun i x => (i.property x).2.2) (fun j y => (j.property y).2.2)
    (fun x ε hε => by obtain ⟨f,hf,hfx⟩ := hF x ε hε; exact ⟨⟨f,hf⟩,hfx⟩)
    (fun y ε hε => by obtain ⟨g,hg,hgy⟩ := hG y ε hε; exact ⟨⟨g,hg⟩,hgy⟩)
    K L hK hL ε hε

lemma bounded_dual_pair_of_cyclic {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (c : X × Y → ℝ) (hc : Continuous c) (Γ : Set (X × Y))
    (hΓ : IsCCyclicallyMonotone c Γ) (a : X × Y) (ha : a ∈ Γ)
    (C : ℝ) (hC : 0 ≤ C) (hc0 : ∀ p, 0 ≤ c p) (hcC : ∀ p, c p ≤ C) :
    ∃ ψ : X → ℝ, ∃ φ : Y → ℝ,
      Measurable ψ ∧ Measurable φ ∧
      (∀ x, -2*C ≤ ψ x ∧ ψ x ≤ 2*C) ∧
      (∀ y, -2*C ≤ φ y ∧ φ y ≤ 2*C) ∧
      (∀ x y, ψ x+φ y ≤ c (x,y)) ∧
      (∀ p ∈ Γ, ψ p.1+φ p.2 = c p) ∧
      HasContinuousEnvelopes ψ (2*C) ∧ HasContinuousEnvelopes φ (2*C) := by
  classical
  letI : Nonempty (TransportChain Γ a) := ⟨TransportChain.base Γ a ha⟩
  letI : Nonempty X := ⟨a.1⟩
  let ψ := chainPotential c Γ a
  have hb (x : X) : BddBelow (range (fun s : TransportChain Γ a => s.cost c x)) :=
    ⟨-C, by rintro _ ⟨s,rfl⟩; exact s.cost_lower c hΓ C hc0 hcC x⟩
  have hψ := (bounded_potential_of_cyclic c Γ hΓ a ha C hc0 hcC).2.2
  have hcont (s : TransportChain Γ a) : Continuous (fun x => s.cost c x) := by
    unfold TransportChain.cost
    fun_prop
  have hψmeas : Measurable ψ :=
    (realInf_upperSemicontinuous (fun (s : TransportChain Γ a) x => s.cost c x) hcont hb).measurable
  have hbφ (y : Y) : BddBelow (range (fun x => c (x,y)-ψ x)) := by
    refine ⟨-C, ?_⟩
    rintro _ ⟨x,rfl⟩
    linarith [hc0 (x,y),(hψ x).2]
  let φ : Y → ℝ := fun y => realInf (fun x => c (x,y)-ψ x)
  have hφ (y : Y) : -C ≤ φ y ∧ φ y ≤ 2*C := by
    constructor
    · exact le_realInf _ (hbφ y) (-C) (by intro x; linarith [hc0 (x,y),(hψ x).2])
    · have h := realInf_le (fun x => c (x,y)-ψ x) (hbφ y) a.1
      linarith [hcC (a.1,y),(hψ a.1).1]
  have hφmeas : Measurable φ :=
    (realInf_upperSemicontinuous (fun x y => c (x,y)-ψ x)
      (fun x => by fun_prop) hbφ).measurable
  have hfeas (x : X) (y : Y) : ψ x+φ y ≤ c (x,y) := by
    have h := realInf_le (fun x => c (x,y)-ψ x) (hbφ y) x
    linarith
  have heq (p : X × Y) (hp : p ∈ Γ) : ψ p.1+φ p.2 = c p := by
    have hs := (bounded_potential_of_cyclic c Γ hΓ a ha C hc0 hcC).2.1 hp
    change cConjugate c (fun x => (ψ x : EReal)) p.2+(ψ p.1 : EReal)=(c p : EReal) at hs
    have he : (φ p.2 : EReal) = cConjugate c (fun x => (ψ x : EReal)) p.2 := by
      dsimp only [φ,cConjugate]
      rw [realInf_coe _ (hbφ p.2)]
      simp only [EReal.coe_sub]
    rw [← he,← EReal.coe_add] at hs
    apply EReal.coe_injective
    simpa only [EReal.coe_add, add_comm] using hs
  refine ⟨ψ,φ,hψmeas,hφmeas,?_,?_,hfeas,heq,?_,?_⟩
  · intro x; constructor <;> linarith [(hψ x).1,(hψ x).2]
  · intro y; constructor <;> linarith [(hφ y).1,(hφ y).2]
  · exact realInf_envelopes (fun (s : TransportChain Γ a) x => s.cost c x) hcont (2*C) (by positivity)
      (fun s x => by linarith [s.cost_lower c hΓ C hc0 hcC x])
      (fun x => by change ψ x ≤ 2*C; linarith [(hψ x).2])
  · exact realInf_envelopes (fun x y => c (x,y)-ψ x) (fun x => by fun_prop)
      (2*C) (by positivity)
      (fun x y => by linarith [hc0 (x,y),(hψ x).2]) (fun y => (hφ y).2)

end MongeKantorovichYao


open Set MeasureTheory Topology
namespace MongeKantorovichYao

lemma integrable_of_bounded {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsFiniteMeasure μ] (f : Z → ℝ) (hf : Measurable f) (D : ℝ)
    (hb : ∀ z, -D ≤ f z ∧ f z ≤ D) : Integrable f μ := by
  apply (integrable_const D).mono' hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs, abs_le]
    exact hb z)

lemma compact_small_real_compl {Z : Type*}
    [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : Set Z, IsCompact K ∧ μ.real Kᶜ ≤ δ := by
  obtain ⟨K,hK,hμ⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (isTightMeasureSet_singleton (μ := μ)) (ENNReal.ofReal δ) (by positivity)
  refine ⟨K,hK,?_⟩
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hμ μ (mem_singleton μ))
  simpa only [measureReal_def, ENNReal.toReal_ofReal hδ.le] using h

lemma continuous_dual_integral_approx {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [Nonempty X] [Nonempty Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : X × Y → ℝ) (hc : Continuous c) (hc0 : ∀ p, 0 ≤ c p)
    (ψ : X → ℝ) (φ : Y → ℝ) (hψ : Integrable ψ μ) (hφ : Integrable φ ν)
    (hfeas : ∀ x y, ψ x+φ y ≤ c (x,y)) (D : ℝ) (hD : 0 ≤ D)
    (hF : HasContinuousEnvelopes ψ D) (hG : HasContinuousEnvelopes φ D)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : BoundedContinuousFunction X ℝ, ∃ g : BoundedContinuousFunction Y ℝ,
      (∀ x y, f x+g y ≤ c (x,y)) ∧
      (∫ x, ψ x ∂μ)+(∫ y, φ y ∂ν) ≤ (∫ x, f x ∂μ)+(∫ y, g y ∂ν)+ε := by
  classical
  let δ := ε/(8*D+4)
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨K,hK,hμK⟩ := compact_small_real_compl μ δ hδ
  obtain ⟨L,hL,hνL⟩ := compact_small_real_compl ν δ hδ
  obtain ⟨f,g,hfg,hf,hg⟩ := continuous_feasible_from_envelopes c hc hc0 ψ φ hfeas
    D hD hF hG K L hK hL (ε/2) (by positivity)
  have hIK : Integrable (Kᶜ.indicator (fun _ : X => 2*D)) μ :=
    (integrable_const _).indicator hK.measurableSet.compl
  have hIL : Integrable (Lᶜ.indicator (fun _ : Y => 2*D)) ν :=
    (integrable_const _).indicator hL.measurableSet.compl
  have h1 := integral_mono hψ ((f.integrable μ).add hIK) hf
  have hgε : Integrable (fun y => g y+ε/2) ν := (g.integrable ν).add (integrable_const (ε/2))
  have h2 := integral_mono hφ (hgε.add hIL) hg
  simp only [Pi.add_apply] at h1 h2
  rw [integral_add (f.integrable μ) hIK,
    integral_indicator_const _ hK.measurableSet.compl, smul_eq_mul] at h1
  rw [integral_add hgε hIL,
    integral_add (g.integrable ν) (integrable_const (ε/2)),
    integral_indicator_const _ hL.measurableSet.compl, smul_eq_mul] at h2
  have hint : (∫ _ : Y, ε/2 ∂ν) = ε/2 := by simp
  rw [hint] at h2
  have hμbound := mul_le_mul_of_nonneg_right hμK (by positivity : 0 ≤ 2*D)
  have hνbound := mul_le_mul_of_nonneg_right hνL (by positivity : 0 ≤ 2*D)
  have hδeq : δ*(8*D+4) = ε := by
    dsimp [δ]
    exact div_mul_cancel₀ ε (by linarith)
  refine ⟨f,g,hfg,?_⟩
  nlinarith

lemma integral_marginals {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (π : Measure (X × Y))
    (hπ : π ∈ transferencePlans μ ν) (ψ : X → ℝ) (φ : Y → ℝ)
    (hψ : Measurable ψ) (hφ : Measurable φ) :
    (∫ p, ψ p.1 ∂π) = (∫ x, ψ x ∂μ) ∧
      (∫ p, φ p.2 ∂π) = (∫ y, φ y ∂ν) := by
  constructor
  · rw [← hπ.2.1]
    exact (integral_map_of_stronglyMeasurable measurable_fst hψ.stronglyMeasurable).symm
  · rw [← hπ.2.2]
    exact (integral_map_of_stronglyMeasurable measurable_snd hφ.stronglyMeasurable).symm

lemma integral_sum_marginals {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (π : Measure (X × Y))
    (hπ : π ∈ transferencePlans μ ν) (ψ : X → ℝ) (φ : Y → ℝ)
    (hψ : Measurable ψ) (hφ : Measurable φ)
    (hψi : Integrable ψ μ) (hφi : Integrable φ ν) :
    (∫ p, ψ p.1+φ p.2 ∂π) = (∫ x, ψ x ∂μ)+(∫ y, φ y ∂ν) := by
  have hψ' : Integrable (fun p : X × Y => ψ p.1) π := by
    apply Integrable.comp_measurable (f := Prod.fst) _ measurable_fst
    rwa [hπ.2.1]
  have hφ' : Integrable (fun p : X × Y => φ p.2) π := by
    apply Integrable.comp_measurable (f := Prod.snd) _ measurable_snd
    rwa [hπ.2.2]
  rw [integral_add hψ' hφ', (integral_marginals μ ν π hπ ψ φ hψ hφ).1,
    (integral_marginals μ ν π hπ ψ φ hψ hφ).2]

end MongeKantorovichYao


open Set MeasureTheory Topology
namespace MongeKantorovichYao

noncomputable def continuousDual {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (c : X × Y → ℝ) : EReal :=
  ⨆ (ψ : BoundedContinuousFunction X ℝ) (φ : BoundedContinuousFunction Y ℝ)
    (_ : ∀ x y, ψ x+φ y ≤ c (x,y)),
    (((∫ x, ψ x ∂μ)+(∫ y, φ y ∂ν) : ℝ) : EReal)

lemma continuousDual_nonneg {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (c : X × Y → ℝ) (hc0 : ∀ p, 0 ≤ c p) :
    0 ≤ continuousDual μ ν c := by
  unfold continuousDual
  apply le_iSup_of_le (BoundedContinuousFunction.const X 0)
  apply le_iSup_of_le (BoundedContinuousFunction.const Y 0)
  apply le_iSup_of_le (show ∀ x y, (BoundedContinuousFunction.const X (0 : ℝ)) x+
    (BoundedContinuousFunction.const Y 0) y ≤ c (x,y) from by simpa using fun x y => hc0 (x,y))
  simp

lemma continuousDual_mono {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) {c d : X × Y → ℝ} (h : c ≤ d) :
    continuousDual μ ν c ≤ continuousDual μ ν d := by
  unfold continuousDual
  refine iSup_le fun f => iSup_le fun g => iSup_le fun hfg => ?_
  exact le_iSup_of_le f (le_iSup_of_le g (le_iSup_of_le
    (fun x y => (hfg x y).trans (h (x,y))) le_rfl))

lemma weak_duality_integrable {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (π : Measure (X × Y))
    (hπ : π ∈ transferencePlans μ ν) (c : X × Y → ℝ) (hci : Integrable c π)
    (ψ : X → ℝ) (φ : Y → ℝ) (hψ : Measurable ψ) (hφ : Measurable φ)
    (hψi : Integrable ψ μ) (hφi : Integrable φ ν)
    (hfeas : ∀ x y, ψ x+φ y ≤ c (x,y)) :
    (∫ x, ψ x ∂μ)+(∫ y, φ y ∂ν) ≤ ∫ p, c p ∂π := by
  have hψ' : Integrable (fun p : X × Y => ψ p.1) π := by
    apply Integrable.comp_measurable (f := Prod.fst) _ measurable_fst
    rwa [hπ.2.1]
  have hφ' : Integrable (fun p : X × Y => φ p.2) π := by
    apply Integrable.comp_measurable (f := Prod.snd) _ measurable_snd
    rwa [hπ.2.2]
  rw [← integral_sum_marginals μ ν π hπ ψ φ hψ hφ hψi hφi]
  exact integral_mono (hψ'.add hφ') hci (fun p => hfeas p.1 p.2)

lemma continuousDual_le_integral {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (π : Measure (X × Y)) (hπ : π ∈ transferencePlans μ ν)
    (c : X × Y → ℝ) (hci : Integrable c π) :
    continuousDual μ ν c ≤ (∫ p, c p ∂π : ℝ) := by
  unfold continuousDual
  refine iSup_le fun f => iSup_le fun g => iSup_le fun hfg => ?_
  apply EReal.coe_le_coe
  exact weak_duality_integrable μ ν π hπ c hci f g f.continuous.measurable
    g.continuous.measurable (f.integrable μ) (g.integrable ν) hfg

lemma bounded_dual_attainment {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : X × Y → ℝ) (hc : Continuous c) (hc0 : ∀ p, 0 ≤ c p)
    (hcb : BddAbove (range c)) :
    ∃ π ∈ transferencePlans μ ν, (∫ p, c p ∂π : ℝ) = continuousDual μ ν c := by
  classical
  obtain ⟨π,hπ,hπC⟩ := general_cyclic_plan μ ν c hc hc0
  letI : IsProbabilityMeasure π := hπ.1
  obtain ⟨a,ha⟩ := π.nonempty_support (IsProbabilityMeasure.ne_zero π)
  letI : Nonempty X := ⟨a.1⟩
  letI : Nonempty Y := ⟨a.2⟩
  obtain ⟨C,hC⟩ := hcb
  have hcC (p : X × Y) : c p ≤ C := hC (mem_range_self p)
  have hC0 : 0 ≤ C := (hc0 a).trans (hcC a)
  have hci : Integrable c π := integrable_of_bounded π c hc.measurable C
    (fun p => ⟨by linarith [hc0 p],hcC p⟩)
  obtain ⟨ψ,φ,hψ,hφ,hψb,hφb,hfeas,heq,hF,hG⟩ :=
    bounded_dual_pair_of_cyclic c hc π.support (support_cyclic c hc π hπC) a ha
      C hC0 hc0 hcC
  have hψi := integrable_of_bounded μ ψ hψ (2*C) (by simpa only [neg_mul] using hψb)
  have hφi := integrable_of_bounded ν φ hφ (2*C) (by simpa only [neg_mul] using hφb)
  have hmem : ∀ᵐ p ∂π, p ∈ π.support := π.support_mem_ae
  have heqae : (fun p => ψ p.1+φ p.2) =ᵐ[π] c :=
    hmem.mono (fun p hp => heq p hp)
  have hint : (∫ x, ψ x ∂μ)+(∫ y, φ y ∂ν) = ∫ p, c p ∂π := by
    rw [← integral_sum_marginals μ ν π hπ ψ φ hψ hφ hψi hφi]
    exact integral_congr_ae heqae
  have hDle := continuousDual_le_integral μ ν π hπ c hci
  have hDtop : continuousDual μ ν c ≠ ⊤ :=
    ne_of_lt (hDle.trans_lt (EReal.coe_lt_top _))
  have hDbot : continuousDual μ ν c ≠ ⊥ :=
    ne_of_gt ((by simp : (⊥ : EReal) < 0).trans_le (continuousDual_nonneg μ ν c hc0))
  have hcl : (∫ p, c p ∂π) ≤ (continuousDual μ ν c).toReal := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨f,g,hfg,hi⟩ := continuous_dual_integral_approx μ ν c hc hc0 ψ φ
      hψi hφi hfeas (2*C) (by positivity) hF hG ε hε
    have hv : (((∫ x, f x ∂μ)+(∫ y, g y ∂ν) : ℝ) : EReal) ≤ continuousDual μ ν c :=
      le_iSup_of_le f (le_iSup_of_le g (le_iSup_of_le hfg le_rfl))
    have hv' := EReal.toReal_le_toReal hv (EReal.coe_ne_bot _) hDtop
    rw [EReal.toReal_coe] at hv'
    rw [hint] at hi
    linarith
  refine ⟨π,hπ,le_antisymm ?_ hDle⟩
  exact (EReal.coe_le_coe hcl).trans (EReal.coe_toReal_le hDbot)

lemma bounded_duality {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : X × Y → ℝ) (hc : Continuous c) (hc0 : ∀ p, 0 ≤ c p)
    (hcb : BddAbove (range c)) :
    (⨅ π ∈ transferencePlans μ ν, ((∫ p, c p ∂π : ℝ) : EReal)) = continuousDual μ ν c := by
  obtain ⟨π,hπ,heq⟩ := bounded_dual_attainment μ ν c hc hc0 hcb
  apply le_antisymm
  · rw [← heq]
    exact iInf_le_of_le π (iInf_le _ hπ)
  · refine le_iInf fun ρ => le_iInf fun hρ => ?_
    letI : IsProbabilityMeasure ρ := hρ.1
    obtain ⟨C,hC⟩ := hcb
    have hci : Integrable c ρ := integrable_of_bounded ρ c hc.measurable C
      (fun p => ⟨by linarith [hc0 p,hC (mem_range_self p)],hC (mem_range_self p)⟩)
    exact continuousDual_le_integral μ ν ρ hρ c hci

end MongeKantorovichYao

open MongeKantorovichYao MeasureTheory
theorem solution {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : X × Y → ℝ) (hc_cont : Continuous c) (hc_nonneg : ∀ p, 0 ≤ c p)
    (hc_bdd : BddAbove (Set.range c)) :
    (⨅ π ∈ transferencePlans μ ν, ((∫ p, c p ∂π : ℝ) : EReal)) =
      ⨆ (ψ : BoundedContinuousFunction X ℝ) (φ : BoundedContinuousFunction Y ℝ)
        (_ : ∀ x y, ψ x + φ y ≤ c (x, y)),
        (((∫ x, ψ x ∂μ) + (∫ y, φ y ∂ν) : ℝ) : EReal) := by
  exact bounded_duality μ ν c hc_cont hc_nonneg hc_bdd

#print axioms solution
