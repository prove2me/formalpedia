-- Prove2me | solution 1 for HetImpatient.FluidSplit.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T14:10:30.100042+00:00
-- url     : https://prove2.me/submissions/c9a828fe-5e2a-4b64-ac55-886711d6e2fc

import Mathlib
import Definitions.Def_HetImpatient_FluidSplit_Model

set_option autoImplicit false

open scoped ENNReal

namespace HetImpatientFluidSplitAux

open Finset

/-- Step size for a ratio move: a direction with a negative coordinate can be followed until
some coordinate of the support hits zero. -/
theorem ratio_step {ι : Type*} [Fintype ι] (x e : ι → ℝ) (hx : ∀ s, 0 ≤ x s)
    (hsupp : ∀ s, x s = 0 → e s = 0) (hneg : ∃ s, e s < 0) :
    ∃ t : ℝ, 0 ≤ t ∧ (∀ s, 0 ≤ x s + t * e s) ∧ ∃ s0, x s0 ≠ 0 ∧ x s0 + t * e s0 = 0 := by
  classical
  obtain ⟨s1, hs1⟩ := hneg
  have hne : (univ.filter (fun s => e s < 0)).Nonempty := ⟨s1, by simp [hs1]⟩
  obtain ⟨s0, hs0mem, hs0min⟩ :=
    Finset.exists_min_image (univ.filter (fun s => e s < 0)) (fun s => x s / (-e s)) hne
  have he0 : e s0 < 0 := by simpa using hs0mem
  refine ⟨x s0 / (-e s0), div_nonneg (hx s0) (by linarith), ?_, s0, ?_, ?_⟩
  · intro s
    by_cases hs : e s < 0
    · have hle := hs0min s (by simp [hs])
      have hpos : 0 < -e s := by linarith
      have : x s0 / (-e s0) * (-e s) ≤ x s := by
        rw [le_div_iff₀ hpos] at hle
        linarith
      nlinarith
    · push Not at hs
      have : 0 ≤ x s0 / (-e s0) := div_nonneg (hx s0) (by linarith)
      have := mul_nonneg this hs
      linarith [hx s]
  · intro h
    have := hsupp s0 h
    linarith
  · have hne0 : e s0 ≠ 0 := ne_of_lt he0
    rw [div_neg, neg_mul, div_mul_cancel₀ _ hne0]
    ring

/-- Sum over a finset subtype rewritten as a sum over the ambient type, via extension by zero. -/
theorem sum_ext_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) (f : S → ℝ)
    (φ : ι → ℝ) :
    ∑ s, (if h : s ∈ S then f ⟨s, h⟩ else 0) * φ s = ∑ t : S, f t * φ t := by
  rw [← Finset.sum_subset (Finset.subset_univ S)]
  · rw [← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl ?_
    intro t _
    simp [t.2]
  · intro s _ hs
    simp [hs]

/-- The support-reduction lemma (the linear-programming basic-solution argument). -/
theorem reduce {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (g : ι → Fin m)
    (a c : ι → ℝ) :
    ∀ (n : ℕ) (x : ι → ℝ), (univ.filter (fun s => x s ≠ 0)).card ≤ n → (∀ s, 0 ≤ x s) →
      ∃ y : ι → ℝ, (∀ s, 0 ≤ y s) ∧
        (∀ i, ∑ s, (if g s = i then y s else 0) = ∑ s, (if g s = i then x s else 0)) ∧
        ∑ s, y s * a s = ∑ s, x s * a s ∧ ∑ s, y s * c s ≤ ∑ s, x s * c s ∧
        (univ.filter (fun s => y s ≠ 0)).card ≤ m + 1 := by
  intro n
  induction n with
  | zero =>
    intro x hcard hx
    refine ⟨x, hx, fun i => rfl, rfl, le_rfl, ?_⟩
    omega
  | succ n ih =>
    intro x hcard hx
    by_cases hsmall : (univ.filter (fun s => x s ≠ 0)).card ≤ m + 1
    · exact ⟨x, hx, fun i => rfl, rfl, le_rfl, hsmall⟩
    push Not at hsmall
    set S := univ.filter (fun s => x s ≠ 0) with hS
    -- the vectors (class indicator, capacity use) in ℝ^{m+1}
    let v : S → (Option (Fin m) → ℝ) := fun t o =>
      match o with
      | none => a t
      | some i => if g t = i then 1 else 0
    have hnotli : ¬ LinearIndependent ℝ v := by
      intro hli
      have h1 := hli.fintype_card_le_finrank
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_option, Fintype.card_fin,
        Fintype.card_coe] at h1
      omega
    rw [Fintype.not_linearIndependent_iff] at hnotli
    obtain ⟨f, hrel, t0, ht0⟩ := hnotli
    let d : ι → ℝ := fun s => if h : s ∈ S then f ⟨s, h⟩ else 0
    have hdsum : ∀ φ : ι → ℝ, ∑ s, d s * φ s = ∑ t : S, f t * φ t :=
      fun φ => sum_ext_zero S f φ
    have hrela : ∑ s, d s * a s = 0 := by
      rw [hdsum]
      have := congrFun hrel none
      simpa [Finset.sum_apply, v] using this
    have hrelg : ∀ i, ∑ s, d s * (if g s = i then 1 else 0) = 0 := by
      intro i
      rw [hdsum]
      have := congrFun hrel (some i)
      simpa [Finset.sum_apply, v] using this
    have hdtot : ∑ s, d s = 0 := by
      have : ∑ s, d s = ∑ i, ∑ s, d s * (if g s = i then 1 else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro s _
        rw [← Finset.mul_sum]
        simp
      rw [this]
      exact Finset.sum_eq_zero (fun i _ => hrelg i)
    have hdS : ∀ s, x s = 0 → d s = 0 := by
      intro s hs
      have : s ∉ S := by simp [hS, hs]
      simp [d, this]
    have hdt0 : d t0.1 ≠ 0 := by
      have : d t0.1 = f t0 := by simp [d, t0.2]
      rw [this]; exact ht0
    have hboth : (∃ s, d s < 0) ∧ (∃ s, 0 < d s) := by
      constructor
      · by_contra h
        push Not at h
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => h s)).mp hdtot t0.1 (mem_univ _)
        exact hdt0 this
      · by_contra h
        push Not at h
        have h' : ∑ s, -d s = 0 := by rw [Finset.sum_neg_distrib, hdtot, neg_zero]
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => by linarith [h s])).mp h' t0.1
          (mem_univ _)
        exact hdt0 (by linarith)
    -- choose the direction that does not raise cost
    obtain ⟨e, hea, heg, hec, heS, heneg⟩ : ∃ e : ι → ℝ, ∑ s, e s * a s = 0 ∧
        (∀ i, ∑ s, e s * (if g s = i then 1 else 0) = 0) ∧ ∑ s, e s * c s ≤ 0 ∧
        (∀ s, x s = 0 → e s = 0) ∧ ∃ s, e s < 0 := by
      by_cases hc : ∑ s, d s * c s ≤ 0
      · exact ⟨d, hrela, hrelg, hc, hdS, hboth.1⟩
      · push Not at hc
        refine ⟨fun s => -d s, ?_, ?_, ?_, ?_, ?_⟩
        · simp [neg_mul, Finset.sum_neg_distrib, hrela]
        · intro i; simp only [neg_mul, Finset.sum_neg_distrib, hrelg i, neg_zero]
        · simp only [neg_mul, Finset.sum_neg_distrib]; linarith
        · intro s hs; simp [hdS s hs]
        · obtain ⟨s, hs⟩ := hboth.2; exact ⟨s, by linarith⟩
    obtain ⟨t, ht, hnn, s0, hs0x, hs0y⟩ := ratio_step x e hx heS heneg
    let x' : ι → ℝ := fun s => x s + t * e s
    have hsub : univ.filter (fun s => x' s ≠ 0) ⊆ S.erase s0 := by
      intro s hs
      simp only [mem_filter, mem_univ, true_and] at hs
      rw [Finset.mem_erase]
      constructor
      · rintro rfl; exact hs hs0y
      · simp only [hS, mem_filter, mem_univ, true_and]
        intro hxs
        apply hs
        simp [x', hxs, heS s hxs]
    have hs0S : s0 ∈ S := by simp [hS, hs0x]
    have hcard' : (univ.filter (fun s => x' s ≠ 0)).card ≤ n := by
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hs0S] at h1
      omega
    obtain ⟨y, hy0, hyg, hya, hyc, hycard⟩ := ih x' hcard' hnn
    refine ⟨y, hy0, ?_, ?_, ?_, hycard⟩
    · intro i
      rw [hyg i]
      have : ∀ s, (if g s = i then x' s else 0) =
          (if g s = i then x s else 0) + t * (e s * (if g s = i then 1 else 0)) := by
        intro s
        by_cases h : g s = i <;> simp [h, x']
      simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, heg i, mul_zero, add_zero]
    · rw [hya]
      simp only [x', add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, hea,
        mul_zero, add_zero]
    · refine le_trans hyc ?_
      simp only [x', add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
      have := mul_nonpos_of_nonneg_of_nonpos ht hec
      linarith

/-- Sum over the compressed index set equals the full sum when dropped terms vanish. -/
theorem sum_compress {J : ℕ} (p : Fin J → Prop) [DecidablePred p] (F : Fin J → ℝ)
    (hF : ∀ j, ¬ p j → F j = 0) :
    ∑ k : Fin (Fintype.card {j // p j}), F ((Fintype.equivFin {j // p j}).symm k).1 =
      ∑ j, F j := by
  rw [Equiv.sum_comp (Fintype.equivFin {j // p j}).symm (fun s => F s.1)]
  rw [← Finset.sum_subtype (univ.filter p) (p := p) (by simp)]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro j _
  by_cases h : p j
  · simp [h]
  · simp [h, hF j h]

/-- Counting: positive counts summing to at most `m+1` over `m` slots. -/
theorem count_struct {m : ℕ} (k : Fin m → ℕ) (hk : ∀ i, 1 ≤ k i) (hs : ∑ i, k i ≤ m + 1) :
    (∀ i l, 1 < k i → 1 < k l → i = l) ∧ (∀ i, 1 < k i → k i = 2) := by
  have hsum : ∑ i, (k i - 1) ≤ 1 := by
    have h1 : ∑ i, k i = ∑ i, (k i - 1) + m := by
      have : ∑ i, k i = ∑ i, ((k i - 1) + 1) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        have := hk i
        omega
      rw [this, Finset.sum_add_distrib]
      simp
    omega
  constructor
  · intro i l hi hl
    by_contra hne
    have : (k i - 1) + (k l - 1) ≤ ∑ j, (k j - 1) := by
      have := Finset.sum_le_sum_of_subset (f := fun j => k j - 1)
        (Finset.subset_univ ({i, l} : Finset (Fin m)))
      rw [Finset.sum_pair hne] at this
      exact this
    omega
  · intro i hi
    have := Finset.single_le_sum (f := fun j => k j - 1) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ i)
    omega

end HetImpatientFluidSplitAux

open HetImpatientFluidSplitAux in
open Finset in
open HetImpatient.FluidSplit in
theorem solution {m : ℕ} (D : HetImpatient.FluidSplit.ClassData m) (hD : D.Standing) (N : ℝ)
    (P : HetImpatient.FluidSplit.Plan m) (hP : HetImpatient.FluidSplit.PlanFeasible D N P) :
    ∃ Q : HetImpatient.FluidSplit.Plan m, HetImpatient.FluidSplit.PlanFeasible D N Q ∧
      HetImpatient.FluidSplit.planCost D Q ≤ HetImpatient.FluidSplit.planCost D P ∧
      ∑ i, (Q.cfg i).J ≤ m + 1 ∧
      (∀ i k, 1 < (Q.cfg i).J → 1 < (Q.cfg k).J → i = k) ∧
      (∀ i, 1 < (Q.cfg i).J → (Q.cfg i).J = 2) := by
  classical
  obtain ⟨hPn, hPN, hPc⟩ := hP
  let ι := Σ i : Fin m, Fin (P.cfg i).J
  let x : ι → ℝ := fun s => (P.cfg s.1).lam s.2
  let a : ι → ℝ := fun s => D.Fbar s.1 ((P.cfg s.1).w s.2) / D.μ s.1
  let c : ι → ℝ := fun s => D.cbar s.1 ((P.cfg s.1).w s.2)
  have hx : ∀ s, 0 ≤ x s := fun s => (hPc s.1).2.1 s.2
  have ha : ∀ s, 0 ≤ a s := fun s =>
    div_nonneg ((hD s.1).2.2.1 _).1 (hD s.1).2.1.le
  obtain ⟨y, hy0, hyg, hya, hyc, hycard⟩ :=
    reduce (fun s : ι => s.1) a c _ x le_rfl hx
  -- class sums
  have hclass : ∀ (z : ι → ℝ) (i : Fin m),
      ∑ s, (if s.1 = i then z s else 0) = ∑ j, z ⟨i, j⟩ := by
    intro z i
    rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (mem_univ i) h
  have hyclass : ∀ i, ∑ j, y ⟨i, j⟩ = D.Λ i := by
    intro i
    rw [← hclass y i, hyg i, hclass x i]
    exact (hPc i).2.2.2.1
  let p : (i : Fin m) → Fin (P.cfg i).J → Prop := fun i j => y ⟨i, j⟩ ≠ 0
  let K : Fin m → ℕ := fun i => Fintype.card {j // p i j}
  let E : (i : Fin m) → {j // p i j} ≃ Fin (K i) := fun i => Fintype.equivFin _
  let Q : HetImpatient.FluidSplit.Plan m :=
    { n := fun i => ∑ j, y ⟨i, j⟩ * a ⟨i, j⟩
      cfg := fun i =>
        { J := K i
          lam := fun k => y ⟨i, ((E i).symm k).1⟩
          w := fun k => (P.cfg i).w ((E i).symm k).1
          n := fun k => y ⟨i, ((E i).symm k).1⟩ * a ⟨i, ((E i).symm k).1⟩ } }
  have hK : ∀ i, 1 ≤ K i := by
    intro i
    by_contra h
    push Not at h
    have h0 : K i = 0 := by omega
    have hall : ∀ j, y ⟨i, j⟩ = 0 := by
      intro j
      by_contra hj
      have : 0 < K i := Fintype.card_pos_iff.mpr ⟨⟨j, hj⟩⟩
      omega
    have := hyclass i
    simp [hall] at this
    linarith [(hD i).1]
  have hcomp : ∀ (i : Fin m) (F : Fin (P.cfg i).J → ℝ), (∀ j, y ⟨i, j⟩ = 0 → F j = 0) →
      ∑ k : Fin (K i), F ((E i).symm k).1 = ∑ j, F j := by
    intro i F hF
    exact sum_compress (p i) F (fun j hj => hF j (by simpa [p] using hj))
  have hKsum : ∑ i, K i = (univ.filter (fun s : ι => y s ≠ 0)).card := by
    rw [Finset.card_filter, Fintype.sum_sigma]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [K, p]
    rw [Fintype.card_subtype, Finset.card_filter]
  have hKle : ∑ i, K i ≤ m + 1 := by rw [hKsum]; exact hycard
  refine ⟨Q, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro i
    show 0 ≤ ∑ j, y ⟨i, j⟩ * a ⟨i, j⟩
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hy0 _) (ha _))
  · -- total capacity
    have h1 : ∑ i, Q.n i = ∑ s, y s * a s := by
      rw [Fintype.sum_sigma]
    rw [h1, hya]
    have h2 : ∑ s, x s * a s ≤ ∑ i, ∑ j, (P.cfg i).n j := by
      rw [Fintype.sum_sigma]
      refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
      have hmu := (hD i).2.1
      have hc := (hPc i).2.2.2.2.1 j
      show (P.cfg i).lam j * (D.Fbar i ((P.cfg i).w j) / D.μ i) ≤ (P.cfg i).n j
      rw [← mul_div_assoc, div_le_iff₀ hmu]
      exact hc
    have h3 : ∑ i, ∑ j, (P.cfg i).n j ≤ ∑ i, P.n i :=
      Finset.sum_le_sum (fun i _ => (hPc i).2.2.2.2.2)
    linarith
  · intro i
    refine ⟨hK i, ?_, ?_, ?_, ?_, ?_⟩
    · intro k; exact hy0 _
    · intro k; exact mul_nonneg (hy0 _) (ha _)
    · show ∑ k : Fin (K i), y ⟨i, ((E i).symm k).1⟩ = D.Λ i
      rw [hcomp i (fun j => y ⟨i, j⟩) (fun j hj => hj)]
      exact hyclass i
    · intro k
      show y ⟨i, ((E i).symm k).1⟩ * D.Fbar i ((P.cfg i).w ((E i).symm k).1) ≤
        y ⟨i, ((E i).symm k).1⟩ * a ⟨i, ((E i).symm k).1⟩ * D.μ i
      have hmu := (hD i).2.1
      apply le_of_eq
      simp only [a]
      field_simp
    · show ∑ k : Fin (K i), y ⟨i, ((E i).symm k).1⟩ * a ⟨i, ((E i).symm k).1⟩ ≤
        ∑ j, y ⟨i, j⟩ * a ⟨i, j⟩
      rw [hcomp i (fun j => y ⟨i, j⟩ * a ⟨i, j⟩) (fun j hj => by simp [hj])]
  · -- cost
    have h1 : HetImpatient.FluidSplit.planCost D Q = ∑ s, y s * c s := by
      unfold HetImpatient.FluidSplit.planCost HetImpatient.FluidSplit.classCost
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact hcomp i (fun j => y ⟨i, j⟩ * c ⟨i, j⟩) (fun j hj => by simp [hj])
    have h2 : HetImpatient.FluidSplit.planCost D P = ∑ s, x s * c s := by
      unfold HetImpatient.FluidSplit.planCost HetImpatient.FluidSplit.classCost
      rw [Fintype.sum_sigma]
    rw [h1, h2]
    exact hyc
  · -- counting
    exact hKle
  · exact (count_struct K hK hKle).1
  · exact (count_struct K hK hKle).2
