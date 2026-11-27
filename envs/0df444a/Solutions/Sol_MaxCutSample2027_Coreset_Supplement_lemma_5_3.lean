-- Prove2me | solution 1 for MaxCutSample2027.Coreset.Supplement.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:40:58.859494+00:00
-- url     : https://prove2.me/submissions/78ef8472-6852-49ea-9e0a-1e48116285f2

import Definitions.Def_MaxCutSample2027_Coreset_Supplement_rFractional
open scoped BigOperators
noncomputable section

set_option autoImplicit false

open MaxCutSample2027
open MaxCutSample2027.Coreset
open MaxCutSample2027.Coreset.Supplement

private def scaledSimplex (r : ℕ) (q : ℝ) : Set (Fin r → ℝ) :=
  {a | (∀ i, 0 ≤ a i) ∧ ∑ i, a i = q}

private theorem scaledSimplex_convex (r : ℕ) (q : ℝ) : Convex ℝ (scaledSimplex r q) := by
  intro a ha b hb α β hα hβ hab
  refine ⟨fun i => add_nonneg (mul_nonneg hα (ha.1 i)) (mul_nonneg hβ (hb.1 i)), ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, ha.2, hb.2, ← add_mul, hab, one_mul]

private theorem scaledSimplex_hull (r : ℕ) [Nonempty (Fin r)] {q : ℝ} (hq : 0 ≤ q) :
    scaledSimplex r q = convexHull ℝ (Set.range fun i : Fin r => Pi.single i q) := by
  classical
  apply subset_antisymm
  · intro a ha
    rcases hq.eq_or_lt with hzero | hpos
    · have ha0 : a = 0 := by
        funext i
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha.1 i)).1 (ha.2.trans hzero.symm) i (Finset.mem_univ i)
      apply subset_convexHull ℝ _
      refine ⟨Classical.choice inferInstance, ?_⟩
      rw [ha0, ← hzero]
      simp
    · have center : (Finset.univ : Finset (Fin r)).centerMass a (fun i => Pi.single i q) = a := by
        funext i
        simp only [Finset.centerMass, ha.2, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
          Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        field_simp [hpos.ne']
      rw [← center]
      exact Finset.univ.centerMass_mem_convexHull (fun i _ => ha.1 i) (ha.2.symm ▸ hpos)
        (fun i _ => ⟨i, rfl⟩)
  · refine convexHull_min ?_ (scaledSimplex_convex r q)
    rintro _ ⟨i, rfl⟩
    refine ⟨?_, by simp⟩
    intro j
    by_cases h : j = i <;> simp [h, hq]

private def flipMatrix {V : Type*} (r : ℕ) : (V → Fin r → ℝ) →ₗ[ℝ] (Fin r → V → ℝ) where
  toFun a := fun j v => a v j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem Zr_hull {V : Type*} [Fintype V] (r : ℕ) [Nonempty (Fin r)] (q : V → ℝ)
    (hq : ∀ v, 0 ≤ q v) : ∃ U : Set (Fin r → V → ℝ), U.Finite ∧ Zr r q = convexHull ℝ U := by
  let U := Set.univ.pi (fun v : V => Set.range fun i : Fin r => Pi.single i (q v))
  refine ⟨flipMatrix r '' U, (Set.Finite.pi (fun _ => Set.finite_range _)).image _, ?_⟩
  rw [← (flipMatrix r).image_convexHull, convexHull_pi]
  ext a
  constructor
  · intro ha
    refine ⟨fun v j => a j v, ?_, rfl⟩
    intro v _
    change (fun j => a j v) ∈ convexHull ℝ (Set.range fun j : Fin r => Pi.single j (q v))
    rw [← scaledSimplex_hull r (hq v)]
    exact ⟨fun j => ha.1 j v, ha.2 v⟩
  · rintro ⟨b, hb, rfl⟩
    have h (v : V) : b v ∈ scaledSimplex r (q v) := by
      rw [scaledSimplex_hull r (hq v)]
      exact hb v (Set.mem_univ _)
    exact ⟨fun j v => (h v).1 j, fun v => (h v).2⟩

private theorem Zr_nonempty {V : Type*} (r : ℕ) [Nonempty (Fin r)] {q : V → ℝ} (hq : ∀ v, 0 ≤ q v) :
    (Zr r q).Nonempty := by
  classical
  let j : Fin r := Classical.choice inferInstance
  refine ⟨fun i v => if i = j then q v else 0, fun i v => ?_, fun v => ?_⟩
  · change 0 ≤ if i = j then q v else 0
    split_ifs <;> first | exact hq v | exact le_rfl
  · simp

private theorem Zr_compact {V : Type*} [Fintype V] (r : ℕ) [Nonempty (Fin r)] {q : V → ℝ}
    (hq : ∀ v, 0 ≤ q v) : IsCompact (Zr r q) := by
  obtain ⟨U, hU, h⟩ := Zr_hull r q hq
  rw [h]
  exact hU.isCompact_convexHull ℝ

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (r : ℕ) (hr : 2 ≤ r)
    (q : V → ℝ) (hq : ∀ v, 0 ≤ q v) :
    ∃ a ∈ Zr r q, fractionalValueR (K A p) a = FKr r (K A p) q ∧
      ∀ j v, a j v = 0 ∨ a j v = q v := by
  classical
  let _ : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  let L := K A p
  let f := fractionalValueR (r := r) L
  have continuous_f : Continuous f := by
    change Continuous (fun a => fractionalValueR L a)
    unfold fractionalValueR bilinear
    apply continuous_finset_sum _
    intro i _
    apply continuous_finset_sum _
    intro j _
    by_cases h : i < j <;> simp only [h, if_true, if_false] <;> fun_prop
  have hne := Zr_nonempty r hq
  have hcomp := Zr_compact r hq
  obtain ⟨a, ha, hmax⟩ := hcomp.exists_isMaxOn hne continuous_f.continuousOn
  have improve (b : Fin r → V → ℝ) (hb : b ∈ Zr r q) (v : V) : ∃ c ∈ Zr r q,
      f b ≤ f c ∧ (∀ j, c j v = 0 ∨ c j v = q v) ∧ ∀ i j : _, i ≠ v → c j i = b j i := by
    let moved (t j : Fin r) (u : V) := if u = v then if j = t then q v else 0 else b j u
    have mem (t : Fin r) : moved t ∈ Zr r q := by
      refine ⟨fun i u => ?_, fun u => ?_⟩
      · dsimp [moved]
        split_ifs <;> first | exact hq v | exact le_rfl | exact hb.1 i u
      · by_cases hu : u = v
        · subst u; simp [moved]
        · simpa [moved, hu] using hb.2 u
    rcases (hq v).eq_or_lt with hzero | hpos
    · refine ⟨b, hb, le_rfl, fun j => Or.inl ?_, fun _ _ _ => rfl⟩
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hb.1 j v)).1
        ((hb.2 v).trans hzero.symm) j (Finset.mem_univ j)
    have diagonal : L v v = 0 := by simp [L, K, hA.2.1]
    have interp (i j : Fin r) (u w : V) :
        q v * (b i u * L u w * b j w) = ∑ t, b t v * (moved t i u * L u w * moved t j w) := by
      by_cases hu : u = v <;> by_cases hw : w = v
      · subst u w
        simp [diagonal]
      · subst u
        simp only [moved, if_true, if_neg hw, ite_mul, mul_ite, zero_mul, mul_zero,
          Finset.sum_ite_eq, Finset.mem_univ]
        ring
      · subst w
        simp only [moved, if_true, if_neg hu, ite_mul, mul_ite, zero_mul, mul_zero,
          Finset.sum_ite_eq, Finset.mem_univ]
        ring
      · simp only [moved, if_neg hu, if_neg hw, ← Finset.sum_mul, hb.2 v]
    have average : q v * f b = ∑ t, b t v * f (moved t) := by
      unfold f fractionalValueR bilinear
      simp only [Finset.mul_sum, mul_ite, mul_zero]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i < j
      · simp only [if_pos hij]
        conv_rhs => rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u _
        conv_rhs => rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun w _ => interp i j u w
      · simp [hij]
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => f (moved i)) Finset.univ_nonempty
    refine ⟨moved i, mem i, ?_, ?_, ?_⟩
    · apply le_of_mul_le_mul_left _ hpos
      rw [average]
      calc
        _ ≤ ∑ t, b t v * f (moved i) := by
          apply Finset.sum_le_sum
          intro t _
          exact mul_le_mul_of_nonneg_left (hi t (Finset.mem_univ t)) (hb.1 t v)
        _ = _ := by rw [← Finset.sum_mul, hb.2 v]
    · intro j
      by_cases hj : j = i <;> simp [moved, hj]
    · intro u j hu
      simp [moved, hu]
  have final (S : Finset V) : ∃ b ∈ Zr r q, IsMaxOn f (Zr r q) b ∧
      ∀ v ∈ S, ∀ j, b j v = 0 ∨ b j v = q v := by
    induction S using Finset.induction_on with
    | empty => exact ⟨a, ha, hmax, by simp⟩
    | @insert v s hv ih =>
      obtain ⟨b, hb, hopt, hdone⟩ := ih
      obtain ⟨c, hc, hbetter, hvertex, hrest⟩ := improve b hb v
      refine ⟨c, hc, isMaxOn_iff.mpr (fun x hx => (hopt hx).trans hbetter), ?_⟩
      intro i hi j
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hvertex j
      · rw [hrest i j (fun h => hv (h ▸ hi))]
        exact hdone i hi j
  obtain ⟨b, hb, hbest, hd⟩ := final Finset.univ
  refine ⟨b, hb, ?_, fun j v => hd v (Finset.mem_univ v) j⟩
  exact le_antisymm (le_csSup hbest.bddAbove ⟨b, hb, rfl⟩)
    (csSup_le (hne.image _) (by rintro _ ⟨c, hc, rfl⟩; exact hbest hc))
