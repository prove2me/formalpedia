-- Prove2me | solution 1 for MaxCutSample2027.Coreset.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:17:01.926874+00:00
-- url     : https://prove2.me/submissions/6cd81dbd-88e6-43b8-93c5-9fab79dcb21b

import Theorems.Thm_MaxCutSample2027_Coreset_lemma_2_3
import Definitions.Def_MaxCutSample2027_Coreset_fractional
open scoped BigOperators

set_option autoImplicit false

open MaxCutSample2027
open MaxCutSample2027.Coreset

open scoped BigOperators

private def push_mass {V I : Type*} [DecidableEq V] (x : I → V) (w : I → ℝ)
    (S : Finset I) (v : V) : ℝ := ∑ i ∈ S.filter (fun i => x i = v), w i

private theorem sum_push_mass {V I : Type*} [Fintype V] [DecidableEq V] (x : I → V) (w : I → ℝ)
    (S : Finset I) (f : V → ℝ) :
    ∑ v, push_mass x w S v * f v = ∑ i ∈ S, w i * f (x i) := by
  unfold push_mass
  simp only [Finset.sum_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.univ) (g := x)
    (fun _ _ => Finset.mem_univ _) (fun i => w i * f (x i))]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2]

private theorem cut_push_mass {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (x : I → V) (w : I → ℝ) (L : V → V → ℝ) (S : Finset I) :
    bilinear L (push_mass x w S) (push_mass x w Sᶜ) =
      cutValue (fun i j => w i * L (x i) (x j) * w j) S := by
  unfold bilinear cutValue
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [sum_push_mass]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp_rw [mul_comm (L (x i) _) (push_mass x w Sᶜ _)]
  rw [sum_push_mass]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem cut_scale {I : Type*} [Fintype I] [DecidableEq I] (G : I → I → ℝ)
    (c : ℝ) (hc : 0 < c) : maxCut (fun i j => G i j / c) = maxCut G / c := by
  have h (S : Finset I) : cutValue (fun i j => G i j / c) S = cutValue G S / c := by
    unfold cutValue
    simp only [Finset.sum_div]
  apply le_antisymm
  · unfold maxCut
    apply Finset.sup'_le
    intro S hS
    rw [h]
    exact div_le_div_of_nonneg_right (Finset.le_sup' _ hS) hc.le
  · obtain ⟨S, hS, hmax⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty : (Finset.univ : Finset (Finset I)).Nonempty)
      (cutValue G)
    change maxCut G = cutValue G S at hmax
    rw [hmax, ← h]
    exact Finset.le_sup' _ hS

private theorem fractional_push_mass {V I : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype I] [DecidableEq I] (A : V → V → ℝ) (p : V → ℝ) (hA : IsWeightMatrix A)
    (hp : IsPositiveProbabilityVector p) (x : I → V) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) :
    FK (K A p) (push_mass x w Finset.univ) =
      maxCut (fun i j => w i * K A p (x i) (x j) * w j) := by
  classical
  let q := push_mass x w Finset.univ
  let G : I → I → ℝ := fun i j => w i * K A p (x i) (x j) * w j
  have hn (S : Finset I) (v : V) : 0 ≤ push_mass x w S v := Finset.sum_nonneg fun i _ => hw i
  have complement (S : Finset I) : q - push_mass x w S = push_mass x w Sᶜ := by
    funext v
    change push_mass x w Finset.univ v - push_mass x w S v = push_mass x w Sᶜ v
    apply sub_eq_of_eq_add
    unfold push_mass
    have dis : Disjoint Sᶜ S := by
      rw [Finset.disjoint_left]
      exact fun i hi hs => (Finset.mem_compl.mp hi) hs
    rw [← Finset.sum_union (dis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
      ← Finset.filter_union, Finset.union_comm Sᶜ S, Finset.union_compl]
  have value (S : Finset I) : bilinear (K A p) (push_mass x w S) (q - push_mass x w S) = cutValue G S := by
    rw [complement]
    exact cut_push_mass x w (K A p) S
  have feasible (S : Finset I) : push_mass x w S ∈ Z q := by
    intro v
    refine ⟨hn S v, ?_⟩
    have h : q v - push_mass x w S v = push_mass x w Sᶜ v := congrFun (complement S) v
    linarith [hn Sᶜ v]
  obtain ⟨a, ha, optimum, extremes⟩ := lemma_2_3 A p hA hp q (hn Finset.univ)
  have bdd : BddAbove ((fun a => bilinear (K A p) a (q - a)) '' Z q) := by
    have box : Z q = Set.Icc 0 q := by ext b; exact forall_and
    have cont : Continuous (fun a => bilinear (K A p) a (q - a)) := by
      unfold bilinear
      simp only [Pi.sub_apply]
      fun_prop
    exact (box ▸ isCompact_Icc : IsCompact (Z q)).image cont |>.bddAbove
  apply le_antisymm
  · let S : Finset I := Finset.univ.filter (fun i => a (x i) = q (x i))
    have hm : push_mass x w S = a := by
      funext v
      by_cases h : a v = q v
      · have eq : S.filter (fun i => x i = v) = Finset.univ.filter (fun i => x i = v) := by
          ext i
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · exact And.right
          · intro hi
            exact ⟨by rwa [hi], hi⟩
        rw [push_mass, eq, h]
        rfl
      · have eq : S.filter (fun i => x i = v) = ∅ := by
          ext i
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          rintro ⟨hi, hi'⟩
          exact h (hi' ▸ hi)
        rw [push_mass, eq, Finset.sum_empty, (extremes v).resolve_right h]
    change FK (K A p) q ≤ maxCut G
    rw [← optimum, ← hm, value]
    exact Finset.le_sup' _ (Finset.mem_univ S)
  · change maxCut G ≤ FK (K A p) q
    unfold maxCut
    apply Finset.sup'_le
    intro S _
    rw [← value]
    exact le_csSup bdd ⟨_, feasible S, rfl⟩

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (k : ℕ) (hk : 1 ≤ k) (x : Fin k → V) :
    FK (K A p) p = maxCut A / (Fintype.card V : ℝ) ^ 2 ∧
    FK (K A p) (empirical x) = maxCut (Ahat A p x) / (Fintype.card V : ℝ) ^ 2 := by
  let N : ℝ := Fintype.card V
  have hN : 0 < N := by
    change (0 : ℝ) < (Fintype.card V : ℝ)
    exact_mod_cast Fintype.card_pos (α := V)
  have hkreal : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have unweighted : push_mass (id : V → V) p Finset.univ = p := by
    funext v
    have hfilter : Finset.univ.filter (fun i : V => id i = v) = {v} := by ext i; simp
    rw [push_mass, hfilter, Finset.sum_singleton]
  have empirical_mass : push_mass x (fun _ => 1 / (k : ℝ)) Finset.univ = empirical x := by
    funext v
    simp only [push_mass, empirical, Finset.sum_const, nsmul_eq_mul, mul_one_div]
  constructor
  · have hpush := fractional_push_mass A p hA hp id p (fun v => (hp.1 v).le)
    rw [unweighted] at hpush
    rw [hpush]
    have scaled : (fun u v => p u * K A p (id u) (id v) * p v) = fun u v => A u v / N ^ 2 := by
      funext u v
      change p u * (A u v / (N ^ 2 * p u * p v)) * p v = _
      field_simp [hN.ne', (hp.1 u).ne', (hp.1 v).ne']
    rw [scaled, cut_scale A (N ^ 2) (by positivity)]
  · rw [← empirical_mass]
    rw [fractional_push_mass A p hA hp x (fun _ => 1 / (k : ℝ)) (fun _ => by positivity)]
    have scaled : (fun i j => (1 / (k : ℝ)) * K A p (x i) (x j) * (1 / (k : ℝ))) =
        fun i j => Ahat A p x i j / N ^ 2 := by
      funext i j
      change (1 / (k : ℝ)) * (A (x i) (x j) / (N ^ 2 * p (x i) * p (x j))) * (1 / (k : ℝ)) =
        (A (x i) (x j) / ((k : ℝ) ^ 2 * p (x i) * p (x j))) / N ^ 2
      field_simp [hN.ne', hkreal.ne', (hp.1 (x i)).ne', (hp.1 (x j)).ne']
    rw [scaled, cut_scale (Ahat A p x) (N ^ 2) (by positivity)]
