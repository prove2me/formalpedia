-- Prove2me | solution 1 for LearnAugFL.CMP.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:59:15.407058+00:00
-- url     : https://prove2.me/submissions/4883bc12-47e0-4fbb-b13e-1d898430111a

import Mathlib
import Definitions.Def_LearnAugFL_CMP_Setting

namespace LearnAugFL.CMP.SharpProof

noncomputable def profile (a b : ℕ) (x : ℝ) : Fin (a + a + b) → Pt :=
  Fin.append (Fin.append (fun _ : Fin a => !₂[-x, 0]) (fun _ : Fin a => !₂[x, 0]))
    (fun _ : Fin b => !₂[0, 1])

lemma profile_multiset (a b : ℕ) (x : ℝ) :
    Finset.univ.val.map (profile a b x) =
      Multiset.replicate a !₂[-x, 0] + Multiset.replicate a !₂[x, 0] +
        Multiset.replicate b !₂[0, 1] := by
  rw [Fin.univ_val_map]
  simp only [profile, List.ofFn_fin_append, List.ofFn_const,
    ← Multiset.coe_add, Multiset.coe_replicate]

lemma profile_sum (a b : ℕ) (x : ℝ) (f : Pt → ℝ) :
    ∑ i, f (profile a b x i) = a * f !₂[-x, 0] + a * f !₂[x, 0] + b * f !₂[0, 1] := by
  have h := congrArg (fun s : Multiset Pt => (s.map f).sum) (profile_multiset a b x)
  simpa [Multiset.map_map, Function.comp_def, List.sum_ofFn] using h

lemma profile_mem (a b : ℕ) (x : ℝ) (i : Fin (a + a + b)) :
    profile a b x i = !₂[0, 1] ∨ profile a b x i = !₂[x, 0] ∨
      profile a b x i = !₂[-x, 0] := by
  have h : profile a b x i ∈ Finset.univ.val.map (profile a b x) := by
    exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  rw [profile_multiset] at h
  simp only [Multiset.mem_add, Multiset.mem_replicate] at h
  aesop

lemma profile_coords (a b k : ℕ) (x : ℝ) (o : Pt) (j : Fin 2) :
    coordValues (profile a b x) o k j =
      Multiset.replicate a ((!₂[-x, 0] : Pt) j) + Multiset.replicate a ((!₂[x, 0] : Pt) j) +
        Multiset.replicate b ((!₂[0, 1] : Pt) j) + Multiset.replicate k (o j) := by
  unfold coordValues
  have h := congrArg (Multiset.map (fun p : Pt => p j)) (profile_multiset a b x)
  simpa only [Multiset.map_map, Function.comp_def, Multiset.map_add, Multiset.map_replicate] using
    congrArg (fun s => s + Multiset.replicate k (o j)) h

end LearnAugFL.CMP.SharpProof

namespace LearnAugFL.CMP.SharpProof

lemma plane_norm (z : Pt) : ‖z‖ = Real.sqrt ((z 0)^2 + (z 1)^2) := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

lemma base_dist (x : ℝ) : dist (!₂[0, 1] : Pt) !₂[x, 0] = Real.sqrt (x^2 + 1) := by
  simp [dist_eq_norm, plane_norm]

lemma origin_base (x : ℝ) (hx : 0 ≤ x) : dist (0 : Pt) !₂[x, 0] = x := by
  simp [dist_eq_norm, plane_norm, Real.sqrt_sq_eq_abs, abs_of_nonneg hx]

lemma origin_upper : dist (0 : Pt) !₂[0, 1] = 1 := by
  simp [dist_eq_norm, plane_norm]

lemma pair_bound (x : ℝ) (z : Pt) :
    2 * (x^2 + z 1) ≤ Real.sqrt (x^2 + 1) *
      (dist z !₂[-x, 0] + dist z !₂[x, 0]) := by
  have hl := real_inner_le_norm ((!₂[0, 1] : Pt) - !₂[-x, 0]) (z - !₂[-x, 0])
  have hr := real_inner_le_norm ((!₂[0, 1] : Pt) - !₂[x, 0]) (z - !₂[x, 0])
  have hnl : ‖(!₂[0, 1] : Pt) - !₂[-x, 0]‖ = Real.sqrt (x^2 + 1) := by
    simpa only [dist_eq_norm, neg_sq] using base_dist (-x)
  have hnr : ‖(!₂[0, 1] : Pt) - !₂[x, 0]‖ = Real.sqrt (x^2 + 1) := base_dist x
  simp only [PiLp.inner_apply, Fin.sum_univ_two, PiLp.sub_apply] at hl hr
  norm_num at hl hr
  rw [hnl, ← dist_eq_norm] at hl
  rw [hnr, ← dist_eq_norm] at hr
  nlinarith

lemma height_bound (z : Pt) : 1 - z 1 ≤ dist z (!₂[0, 1] : Pt) := by
  have h := real_inner_le_norm (!₂[0, 1] : Pt) ((!₂[0, 1] : Pt) - z)
  have hn : ‖(!₂[0, 1] : Pt)‖ = 1 := by simp [plane_norm]
  rw [hn, one_mul, ← dist_eq_norm, dist_comm] at h
  simpa [PiLp.inner_apply, Fin.sum_univ_two] using h

lemma profile_opt (a b : ℕ) (x : ℝ) (hx : 0 < x)
    (hbalance : (b : ℝ) * x = 2 * a) : IsOpt (profile a b x) !₂[0, 1] := by
  intro z
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [profile_sum, profile_sum, base_dist, base_dist, neg_sq, dist_self, mul_zero, add_zero]
  let D := Real.sqrt (x^2 + 1)
  have hD : 0 < D := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg x])
  have hDsq : D^2 = x^2 + 1 := Real.sq_sqrt (by nlinarith [sq_nonneg x])
  have hxD : x ≤ D := by nlinarith
  have hbalance' : 2 * (a : ℝ) ≤ b * D := by
    nlinarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
  have hp := mul_le_mul_of_nonneg_left (pair_bound x z) (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
  have hh := mul_le_mul_of_nonneg_left (height_bound z) (show (0 : ℝ) ≤ 2*a by positivity)
  have hb := mul_le_mul_of_nonneg_right hbalance' (dist_nonneg : 0 ≤ dist z (!₂[0, 1] : Pt))
  change (a : ℝ) * (2 * (x^2 + z 1)) ≤ a * (D * (dist z !₂[-x, 0] + dist z !₂[x, 0])) at hp
  apply (mul_le_mul_iff_right₀ hD).mp
  have hs := congrArg (fun r : ℝ => (a : ℝ) * r) hDsq
  nlinarith only [hp, hh, hb, hs]

end LearnAugFL.CMP.SharpProof

namespace LearnAugFL.CMP.SharpProof

-- Complete helper proof reused from facility-ratio, with local namespace.
lemma sort_replicate_add (a b : ℝ) (n k : ℕ) (hab : a ≤ b) :
    (Multiset.replicate n a + Multiset.replicate k b).sort (· ≤ ·) =
      List.replicate n a ++ List.replicate k b := by
  have hsort : (List.replicate n a ++ List.replicate k b).Pairwise (· ≤ ·) := by
    rw [List.pairwise_append]
    refine ⟨List.pairwise_replicate_of_refl, List.pairwise_replicate_of_refl, ?_⟩
    intro x hx y hy
    have hx' : x = a := (List.mem_replicate.mp hx).2
    have hy' : y = b := (List.mem_replicate.mp hy).2
    simpa only [hx', hy'] using hab
  rw [← Multiset.coe_replicate, ← Multiset.coe_replicate, Multiset.coe_add,
    Multiset.coe_sort]
  exact List.mergeSort_eq_self _ hsort

lemma sort_three (a b c : ℝ) (n m k : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    (Multiset.replicate n a + Multiset.replicate m b + Multiset.replicate k c).sort (· ≤ ·) =
      (List.replicate n a ++ List.replicate m b) ++ List.replicate k c := by
  have hs : ((List.replicate n a ++ List.replicate m b) ++ List.replicate k c).Pairwise (· ≤ ·) := by
    simp only [List.pairwise_append, List.pairwise_replicate_of_refl, true_and,
      List.mem_append, List.mem_replicate]
    constructor
    · intro x hx y hy
      simpa [hx.2, hy.2] using hab
    · intro x hx y hy
      rcases hx with hx | hx
      · simpa [hx.2, hy.2] using hab.trans hbc
      · simpa [hx.2, hy.2] using hbc
  rw [← Multiset.coe_replicate, ← Multiset.coe_replicate, ← Multiset.coe_replicate,
    Multiset.coe_add, Multiset.coe_add, Multiset.coe_sort]
  exact List.mergeSort_eq_self _ hs

lemma median_symmetric (a m : ℕ) (hm : 0 < m) (x : ℝ) (hx : 0 ≤ x) :
    lowerMedian (Multiset.replicate a (-x) + Multiset.replicate m 0 + Multiset.replicate a x) = 0 := by
  have hlow : a ≤ (a + m + a + 1) / 2 - 1 := by omega
  have hhigh : (a + m + a + 1) / 2 - 1 < a + m := by omega
  unfold lowerMedian
  simp only [Multiset.card_add, Multiset.card_replicate]
  rw [sort_three (-x) 0 x a m a (neg_nonpos.mpr hx) hx, List.getD_append]
  · rw [List.getD_append_right]
    · apply List.getD_replicate 0
      simp only [List.length_replicate]
      omega
    · simpa only [List.length_replicate] using hlow
  · simpa only [List.length_append, List.length_replicate] using hhigh

lemma median_half (m : ℕ) (hm : 0 < m) :
    lowerMedian (Multiset.replicate m (0 : ℝ) + Multiset.replicate m 1) = 0 := by
  unfold lowerMedian
  simp only [Multiset.card_add, Multiset.card_replicate]
  rw [sort_replicate_add 0 1 m m (by norm_num), List.getD_append]
  · apply List.getD_replicate 0
    omega
  · simp only [List.length_replicate]
    omega

lemma cmp_consistency (a b k : ℕ) (ha : 0 < a) (hbk : b + k = a + a)
    (x : ℝ) (hx : 0 ≤ x) : cmp (profile a b x) !₂[0, 1] k = 0 := by
  have hxcoords : coordValues (profile a b x) !₂[0, 1] k 0 =
      Multiset.replicate a (-x) + Multiset.replicate (b+k) 0 + Multiset.replicate a x := by
    rw [profile_coords]
    simp only [PiLp.toLp_apply, Matrix.cons_val_zero]
    rw [Multiset.replicate_add]
    ac_rfl
  have hycoords : coordValues (profile a b x) !₂[0, 1] k 1 =
      Multiset.replicate (a+a) (0 : ℝ) + Multiset.replicate (a+a) 1 := by
    rw [profile_coords]
    change Multiset.replicate a 0 + Multiset.replicate a 0 + Multiset.replicate b 1 +
      Multiset.replicate k 1 = _
    calc
      Multiset.replicate a (0 : ℝ) + Multiset.replicate a 0 + Multiset.replicate b 1 +
          Multiset.replicate k 1 = Multiset.replicate (a+a) 0 + Multiset.replicate (b+k) 1 := by
        simp only [Multiset.replicate_add, add_assoc]
      _ = _ := by rw [hbk]
  ext j
  fin_cases j
  · change lowerMedian (coordValues (profile a b x) _ k 0) = 0
    rw [hxcoords, median_symmetric a (b+k) (by omega) x hx]
  · change lowerMedian (coordValues (profile a b x) _ k 1) = 0
    rw [hycoords, median_half (a+a) (by omega)]

lemma cmp_robustness (a b k : ℕ) (hb : 0 < b) (hbk : a + a + k = b)
    (x : ℝ) (hx : 0 ≤ x) : cmp (profile a b x) 0 k = 0 := by
  have hxcoords : coordValues (profile a b x) 0 k 0 =
      Multiset.replicate a (-x) + Multiset.replicate (b+k) 0 + Multiset.replicate a x := by
    rw [profile_coords]
    simp only [PiLp.toLp_apply, Matrix.cons_val_zero, PiLp.zero_apply]
    rw [Multiset.replicate_add]
    ac_rfl
  have hycoords : coordValues (profile a b x) 0 k 1 =
      Multiset.replicate b (0 : ℝ) + Multiset.replicate b 1 := by
    rw [profile_coords]
    change Multiset.replicate a 0 + Multiset.replicate a 0 + Multiset.replicate b 1 +
      Multiset.replicate k 0 = _
    calc
      Multiset.replicate a (0 : ℝ) + Multiset.replicate a 0 + Multiset.replicate b 1 +
          Multiset.replicate k 0 = Multiset.replicate (a+a+k) 0 + Multiset.replicate b 1 := by
        simp only [Multiset.replicate_add]
        ac_rfl
      _ = _ := by rw [hbk]
  ext j
  fin_cases j
  · change lowerMedian (coordValues (profile a b x) _ k 0) = 0
    rw [hxcoords, median_symmetric a (b+k) (by omega) x hx]
  · change lowerMedian (coordValues (profile a b x) _ k 1) = 0
    rw [hycoords, median_half b hb]

end LearnAugFL.CMP.SharpProof

namespace LearnAugFL.CMP.SharpProof

lemma profile_ratio (a b k : ℕ) (ha : 0 < a) (x : ℝ) (hx : 0 ≤ x) (o : Pt)
    (hcmp : cmp (profile a b x) o k = 0) :
    ratio (profile a b x) o !₂[0, 1] k =
      (2*a*x+b) / (2*a*Real.sqrt (x^2+1)) := by
  have hn : ((a+a+b : ℕ) : ℝ) ≠ 0 := by positivity
  unfold ratio ucost
  rw [hcmp, div_div_div_cancel_right₀ hn, profile_sum, profile_sum]
  have hneg : dist (0 : Pt) !₂[-x, 0] = x := by
    simp [dist_eq_norm, plane_norm, Real.sqrt_sq_eq_abs, abs_of_nonneg hx]
  rw [hneg, origin_base x hx, origin_upper, base_dist, base_dist, neg_sq,
    dist_self, mul_zero, add_zero]
  congr 1 <;> ring

lemma sharp_ratio_algebra (A B a b : ℝ) (hA : 0 < A) (hB : 0 < B)
    (ha : 0 < a) (hbal : b*A=2*a*B) :
    (2*a*(A/B)+b) / (2*a*Real.sqrt ((A/B)^2+1)) = Real.sqrt (A^2+B^2)/A := by
  let S := Real.sqrt (A^2+B^2)
  have hSpos : 0 < S := Real.sqrt_pos.mpr (by positivity)
  have hSsq : S^2=A^2+B^2 := Real.sq_sqrt (by positivity)
  have hroot : Real.sqrt ((A/B)^2+1) = S/B := by
    have hsq : (S/B)^2 = (A/B)^2+1 := by
      field_simp
      nlinarith only [hSsq]
    rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_pos (div_pos hSpos hB)]
  rw [hroot]
  apply (div_eq_iff (mul_ne_zero (mul_ne_zero (by norm_num) ha.ne')
    (div_ne_zero hSpos.ne' hB.ne'))).mpr
  field_simp
  change A * (2*a*A+B*b) = 2*a*S*S
  linear_combination B*hbal - 2*a*hSsq

end LearnAugFL.CMP.SharpProof

namespace LearnAugFL.CMP.SharpProof

lemma construct (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hc : ∃ N K : ℕ, Admissible c N K) :
    (∃ (n k : ℕ) (P : Fin n → Pt), COA_C c n k P ∧
        ratio P !₂[0, 1] !₂[0, 1] k = Real.sqrt (2*c^2+2)/(1+c)) ∧
    (∃ (n k : ℕ) (P : Fin n → Pt), COA_R c n k P ∧
        ratio P 0 !₂[0, 1] k = Real.sqrt (2*c^2+2)/(1-c)) := by
  obtain ⟨N, K, hN, hK⟩ := hc
  have hNp : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have hKN : K < N := by
    have h := mul_lt_mul_of_pos_right hc1 hNr
    rw [← hK, one_mul] at h
    exact_mod_cast h
  have hsub : (↑(N-K) : ℝ) = (N:ℝ)-K := Nat.cast_sub hKN.le
  have hplus : 0 < 1+c := by linarith
  have hminus : 0 < 1-c := by linarith
  have hsq : (1+c)^2+(1-c)^2=2*c^2+2 := by ring
  constructor
  · let a := N+K
    let b := 2*(N-K)
    let k := 4*K
    let x := (1+c)/(1-c)
    have ha : 0 < a := by dsimp [a]; omega
    have hx : 0 < x := div_pos hplus hminus
    have hbal : (b:ℝ)*(1+c)=2*(a:ℝ)*(1-c) := by
      dsimp [a,b]
      push_cast
      rw [hsub]
      nlinarith only [hK]
    have hbalance : (b:ℝ)*x=2*a := by
      dsimp [x]
      rw [← mul_div_assoc, div_eq_iff hminus.ne']
      exact hbal
    have hcount : b+k=a+a := by dsimp [a,b,k]; omega
    have hcmp := cmp_consistency a b k ha hcount x hx.le
    refine ⟨a+a+b, k, profile a b x, ?_, ?_⟩
    · refine ⟨?_, profile_opt a b x hx hbalance, hcmp, x, hx.le, profile_mem a b x⟩
      constructor
      · omega
      · dsimp [a,b,k]
        push_cast
        rw [hsub]
        nlinarith only [hK]
    · rw [profile_ratio a b k ha x hx.le _ hcmp]
      change (2*(a:ℝ)*((1+c)/(1-c))+(b:ℝ)) /
        (2*(a:ℝ)*Real.sqrt (((1+c)/(1-c))^2+1)) = _
      rw [sharp_ratio_algebra (1+c) (1-c) a b hplus hminus (by exact_mod_cast ha) hbal, hsq]
  · let a := N-K
    let b := 2*(N+K)
    let k := 4*K
    let x := (1-c)/(1+c)
    have ha : 0 < a := by dsimp [a]; omega
    have hb : 0 < b := by dsimp [b]; omega
    have hx : 0 < x := div_pos hminus hplus
    have hbal : (b:ℝ)*(1-c)=2*(a:ℝ)*(1+c) := by
      dsimp [a,b]
      push_cast
      rw [hsub]
      nlinarith only [hK]
    have hbalance : (b:ℝ)*x=2*a := by
      dsimp [x]
      rw [← mul_div_assoc, div_eq_iff hplus.ne']
      exact hbal
    have hcount : a+a+k=b := by dsimp [a,b,k]; omega
    have hcmp := cmp_robustness a b k hb hcount x hx.le
    refine ⟨a+a+b, k, profile a b x, ?_, ?_⟩
    · refine ⟨?_, profile_opt a b x hx hbalance, hcmp, x, hx.le, profile_mem a b x⟩
      constructor
      · omega
      · dsimp [a,b,k]
        push_cast
        rw [hsub]
        nlinarith only [hK]
    · rw [profile_ratio a b k ha x hx.le _ hcmp]
      change (2*(a:ℝ)*((1-c)/(1+c))+(b:ℝ)) /
        (2*(a:ℝ)*Real.sqrt (((1-c)/(1+c))^2+1)) = _
      rw [sharp_ratio_algebra (1-c) (1+c) a b hminus hplus (by exact_mod_cast ha) hbal,
        add_comm ((1-c)^2), hsq]

end LearnAugFL.CMP.SharpProof

open LearnAugFL.CMP

theorem solution (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (hc : ∃ n₀ k₀ : ℕ, Admissible c n₀ k₀) :
    (∃ (n k : ℕ) (P : Fin n → Pt), COA_C c n k P ∧
        ratio P !₂[0, 1] !₂[0, 1] k = Real.sqrt (2 * c ^ 2 + 2) / (1 + c)) ∧
    (∃ (n k : ℕ) (Q : Fin n → Pt), COA_R c n k Q ∧
        ratio Q 0 !₂[0, 1] k = Real.sqrt (2 * c ^ 2 + 2) / (1 - c)) := by
  exact SharpProof.construct c hc0 hc1 hc

