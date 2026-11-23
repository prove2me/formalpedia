-- Prove2me | solution 1 for L1Sparsifiers.Main.corollary_19
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:36:44.502902+00:00
-- url     : https://prove2.me/submissions/79106029-7779-4694-b61f-ab493587e2ef

import Definitions.Def_L1Sparsifiers_Main_UniformCube
import Definitions.Def_L1Sparsifiers_Main_SeparatelyConvex
import Definitions.Def_PSDPolyApprox_expect
import Theorems.Thm_L1Sparsifiers_Main_lemma_18

open MeasureTheory PSDPolyApprox L1Sparsifiers.Main

namespace AuxCor19

lemma unit_cast_cases (u : ℤˣ) : ((u : ℤ) : ℝ) = 1 ∨ ((u : ℤ) : ℝ) = -1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

lemma unit_cast_sq (u : ℤˣ) : ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
  rcases unit_cast_cases u with h | h <;> rw [h] <;> norm_num

lemma card_cube (m : ℕ) : Fintype.card (Cube m) = 2 ^ m := by
  have h2 : Fintype.card ℤˣ = 2 := by
    have huniv : (Finset.univ : Finset ℤˣ) = {1, -1} := by
      ext u; simp [Int.units_eq_one_or u]
    change (Finset.univ : Finset ℤˣ).card = 2
    rw [huniv, Finset.card_pair (by decide : (1 : ℤˣ) ≠ -1)]
  simp [Cube, h2]

lemma sepConvex_upper_bound {m : ℕ} {f : (Fin m → ℝ) → ℝ}
    (hnn : ∀ x ∈ cube m, 0 ≤ f x) (hsep : SepConvexOn (Set.Icc (-1 : ℝ) 1) f)
    {q : Fin m → ℝ} (hq : q ∈ cube m) :
    f q ≤ ∑ σ : Cube m, f (vertex σ) := by
  classical
  have hq_mem : ∀ i : Fin m, q i ∈ Set.Icc (-1 : ℝ) 1 := fun i => ⟨hq.1 i, hq.2 i⟩
  have hvert_mem : ∀ σ : Cube m, vertex σ ∈ cube m := by
    intro σ
    refine ⟨fun i => ?_, fun i => ?_⟩ <;>
    · rcases unit_cast_cases (σ i) with h1 | hm1
      · simp [vertex, h1]
      · simp [vertex, hm1]
  let G : Finset (Fin m) → ℝ := fun S =>
    ((2 : ℝ) ^ m)⁻¹ * ∑ σ : Cube m,
      (∏ i ∈ S, (1 + q i * vertex σ i)) * f (fun i => if i ∈ S then vertex σ i else q i)
  have hG_empty : G ∅ = f q := by
    simp only [G, Finset.prod_empty, Finset.notMem_empty, ↓reduceIte, one_mul,
      Finset.sum_const, Finset.card_univ, card_cube, nsmul_eq_mul]
    rw [Nat.cast_pow, Nat.cast_ofNat, inv_mul_cancel_left₀ (by positivity)]
  have hG_step : ∀ (S : Finset (Fin m)) (j : Fin m), j ∉ S → G S ≤ G (insert j S) := by
    intro S j hjS
    let flip : Cube m → Cube m := fun σ => Function.update σ j (-σ j)
    have hflip_bij : Function.Bijective flip := by
      refine Function.Involutive.bijective (fun σ => ?_)
      ext i
      by_cases hij : i = j
      · subst hij; simp [flip]
      · simp [flip, hij]
    let term : Finset (Fin m) → Cube m → ℝ := fun T σ =>
      (∏ i ∈ T, (1 + q i * vertex σ i)) * f (fun i => if i ∈ T then vertex σ i else q i)
    have hsum_flip : ∑ σ : Cube m, term (insert j S) σ =
        2⁻¹ * ∑ σ : Cube m, (term (insert j S) σ + term (insert j S) (flip σ)) := by
      rw [Finset.sum_add_distrib]
      have heq : ∑ σ : Cube m, term (insert j S) (flip σ) = ∑ σ : Cube m, term (insert j S) σ :=
        Fintype.sum_bijective flip hflip_bij _ _ (fun _ => rfl)
      rw [heq]
      ring
    have hpair : ∀ σ : Cube m,
        term S σ ≤ 2⁻¹ * (term (insert j S) σ + term (insert j S) (flip σ)) := by
      intro σ
      let w : Fin m → ℝ := fun i => if i ∈ S then vertex σ i else q i
      have hw : ∀ i, w i ∈ Set.Icc (-1 : ℝ) 1 := by
        intro i
        simp only [w]
        split_ifs
        · rcases unit_cast_cases (σ i) with h1 | hm1
          · simp [vertex, h1]
          · simp [vertex, hm1]
        · exact hq_mem i
      have hw_j : Function.update w j (q j) = w := by
        ext i
        by_cases hij : i = j
        · subst hij; simp [w, hjS]
        · simp [hij]
      have hconv := hsep w hw j
      have ha_nn : 0 ≤ (1 + q j) / 2 := by linarith [(hq_mem j).1]
      have hb_nn : 0 ≤ (1 - q j) / 2 := by linarith [(hq_mem j).2]
      have hab : (1 + q j) / 2 + (1 - q j) / 2 = 1 := by ring
      have hjens : f w ≤ (1 + q j) / 2 * f (Function.update w j 1) +
          (1 - q j) / 2 * f (Function.update w j (-1)) := by
        have h := hconv.2 (by norm_num : (1 : ℝ) ∈ Set.Icc (-1) 1)
          (by norm_num : (-1 : ℝ) ∈ Set.Icc (-1) 1) ha_nn hb_nn hab
        simp only [smul_eq_mul] at h
        have hcomb : (1 + q j) / 2 * 1 + (1 - q j) / 2 * -1 = q j := by ring
        rwa [hcomb, hw_j] at h
      have hprod_nn : 0 ≤ ∏ i ∈ S, (1 + q i * vertex σ i) := by
        refine Finset.prod_nonneg (fun i _ => ?_)
        rcases unit_cast_cases (σ i) with h1 | hm1
        · simp only [vertex, h1, mul_one]; linarith [(hq_mem i).1]
        · simp only [vertex, hm1, mul_neg, mul_one]; linarith [(hq_mem i).2]
      have hprod_flip : ∏ i ∈ S, (1 + q i * vertex (flip σ) i) =
          ∏ i ∈ S, (1 + q i * vertex σ i) := by
        refine Finset.prod_congr rfl (fun i hi => ?_)
        have hij : i ≠ j := fun h => hjS (h ▸ hi)
        simp [flip, vertex, hij]
      have hvec_σ : (fun i => if i ∈ insert j S then vertex σ i else q i) =
          Function.update w j (vertex σ j) := by
        ext i; by_cases hij : i = j
        · subst hij; simp
        · simp [w, hij]
      have hvec_flip : (fun i => if i ∈ insert j S then vertex (flip σ) i else q i) =
          Function.update w j (-vertex σ j) := by
        ext i; by_cases hij : i = j
        · subst hij; simp [flip, vertex]
        · simp [w, flip, vertex, hij]
      have hflip_j : vertex (flip σ) j = -vertex σ j := by simp [flip, vertex]
      have hrhs_eq : 2⁻¹ * (term (insert j S) σ + term (insert j S) (flip σ)) =
          (∏ i ∈ S, (1 + q i * vertex σ i)) *
            ((1 + q j) / 2 * f (Function.update w j 1) +
              (1 - q j) / 2 * f (Function.update w j (-1))) := by
        simp only [term, Finset.prod_insert hjS, hprod_flip, hvec_σ, hvec_flip, hflip_j]
        rcases unit_cast_cases (σ j) with h1 | hm1
        · simp only [vertex] at h1 ⊢; rw [h1]; norm_num; ring
        · simp only [vertex] at hm1 ⊢; rw [hm1]; norm_num; ring
      rw [hrhs_eq]
      exact mul_le_mul_of_nonneg_left hjens hprod_nn
    simp only [G]
    rw [hsum_flip]
    have hsum_le : ∑ σ : Cube m, term S σ ≤
        2⁻¹ * ∑ σ : Cube m, (term (insert j S) σ + term (insert j S) (flip σ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun σ _ => hpair σ)
    exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
  have hmono : ∀ S : Finset (Fin m), G ∅ ≤ G S := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact le_rfl
    | @insert j S hjS ih => exact ih.trans (hG_step S j hjS)
  have h1 := hmono Finset.univ
  rw [hG_empty] at h1
  refine h1.trans ?_
  simp only [G, Finset.mem_univ, ↓reduceIte]
  have hprod_le : ∀ σ : Cube m, ∏ i : Fin m, (1 + q i * vertex σ i) ≤ (2 : ℝ) ^ m := by
    intro σ
    calc ∏ i : Fin m, (1 + q i * vertex σ i)
        ≤ ∏ _ : Fin m, (2 : ℝ) := by
          refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
          · rcases unit_cast_cases (σ i) with h1 | hm1
            · simp only [vertex, h1, mul_one]; linarith [(hq_mem i).1]
            · simp only [vertex, hm1, mul_neg, mul_one]; linarith [(hq_mem i).2]
          · rcases unit_cast_cases (σ i) with h1 | hm1
            · simp only [vertex, h1, mul_one]; linarith [(hq_mem i).2]
            · simp only [vertex, hm1, mul_neg, mul_one]; linarith [(hq_mem i).1]
      _ = (2 : ℝ) ^ m := by simp
  calc ((2 : ℝ) ^ m)⁻¹ * ∑ σ : Cube m, (∏ i : Fin m, (1 + q i * vertex σ i)) * f (vertex σ)
      ≤ ((2 : ℝ) ^ m)⁻¹ * ∑ σ : Cube m, (2 : ℝ) ^ m * f (vertex σ) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_right (hprod_le σ)
              (hnn (vertex σ) (hvert_mem σ)))) (by positivity)
    _ = ∑ σ : Cube m, f (vertex σ) := by
        rw [← Finset.mul_sum, inv_mul_cancel_left₀ (by positivity)]

lemma convex_Icc_lipschitz {φ : ℝ → ℝ} {M r : ℝ} (hr1 : r < 1)
    (hconv : ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) φ)
    (hbdd : ∀ u ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ φ u ∧ φ u ≤ M)
    {u v : ℝ} (hu : u ∈ Set.Icc (-r) r) (hv : v ∈ Set.Icc (-r) r) :
    |φ u - φ v| ≤ M / (1 - r) * |u - v| := by
  have hM0 : 0 ≤ M := (hbdd 0 ⟨by norm_num, by norm_num⟩).1.trans (hbdd 0 ⟨by norm_num, by norm_num⟩).2
  have h1mr : 0 < 1 - r := by linarith
  have one_dir : ∀ a b : ℝ, a ∈ Set.Icc (-r) r → b ∈ Set.Icc (-r) r → a < b →
      |φ a - φ b| ≤ M / (1 - r) * (b - a) := by
    intro a b ha hb hab
    have ha_Icc : a ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [ha.1], by linarith [ha.2]⟩
    have hb_Icc : b ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hb.1], by linarith [hb.2]⟩
    have h1ma : 0 < 1 - a := by linarith [ha.2]
    set θ : ℝ := (b - a) / (1 - a)
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith) h1ma.le
    have hθ1 : 0 ≤ 1 - θ := by
      have : b - a ≤ 1 - a := by linarith [hb.2]
      linarith [(div_le_one h1ma).mpr this]
    have hconv1 := hconv.2 ha_Icc (by norm_num : (1 : ℝ) ∈ Set.Icc (-1) 1) hθ1 hθ0 (by ring)
    simp only [smul_eq_mul] at hconv1
    have hcomb1 : (1 - θ) * a + θ * 1 = b := by
      simp only [θ]; field_simp [h1ma.ne']; ring
    rw [hcomb1] at hconv1
    have hdiff1 : φ b - φ a ≤ M / (1 - r) * (b - a) := by
      have hφ1 := (hbdd 1 (by norm_num)).2
      have hφa := (hbdd a ha_Icc).1
      have hθ_le : θ ≤ (b - a) / (1 - r) :=
        div_le_div_of_nonneg_left (by linarith) h1mr (by linarith [ha.2])
      calc φ b - φ a
          ≤ θ * (φ 1 - φ a) := by linarith
        _ ≤ θ * M := mul_le_mul_of_nonneg_left (by linarith) hθ0
        _ ≤ (b - a) / (1 - r) * M := mul_le_mul_of_nonneg_right hθ_le hM0
        _ = M / (1 - r) * (b - a) := by ring
    have hb1 : 0 < b + 1 := by linarith [hb.1]
    set η : ℝ := (b - a) / (b + 1)
    have hη0 : 0 ≤ η := div_nonneg (by linarith) hb1.le
    have hη1 : 0 ≤ 1 - η := by
      have : b - a ≤ b + 1 := by linarith [ha.1]
      linarith [(div_le_one hb1).mpr this]
    have hconv2 := hconv.2 hb_Icc (by norm_num : (-1 : ℝ) ∈ Set.Icc (-1) 1) hη1 hη0 (by ring)
    simp only [smul_eq_mul] at hconv2
    have hcomb2 : (1 - η) * b + η * -1 = a := by
      simp only [η]; field_simp [hb1.ne']; ring
    rw [hcomb2] at hconv2
    have hdiff2 : φ a - φ b ≤ M / (1 - r) * (b - a) := by
      have hφm1 := (hbdd (-1) (by norm_num)).2
      have hφb := (hbdd b hb_Icc).1
      have hη_le : η ≤ (b - a) / (1 - r) :=
        div_le_div_of_nonneg_left (by linarith) h1mr (by linarith [hb.1])
      calc φ a - φ b
          ≤ η * (φ (-1) - φ b) := by linarith
        _ ≤ η * M := mul_le_mul_of_nonneg_left (by linarith) hη0
        _ ≤ (b - a) / (1 - r) * M := mul_le_mul_of_nonneg_right hη_le hM0
        _ = M / (1 - r) * (b - a) := by ring
    exact abs_sub_le_iff.mpr ⟨hdiff2, hdiff1⟩
  rcases lt_trichotomy u v with huv | rfl | hvu
  · rw [abs_of_neg (sub_neg.mpr huv), neg_sub]
    exact one_dir u v hu hv huv
  · simp
  · rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hvu)]
    exact one_dir v u hv hu hvu

def openCube (m : ℕ) : Set (Fin m → ℝ) := Set.pi Set.univ (fun _ => Set.Ioo (-1 : ℝ) 1)

def posCube (m : ℕ) : Set (Fin m → ℝ) := Set.pi Set.univ (fun _ => Set.Ioo (0 : ℝ) 1)

lemma sepConvex_continuousOn_openCube {m : ℕ} {f : (Fin m → ℝ) → ℝ}
    (hnn : ∀ x ∈ cube m, 0 ≤ f x) (hsep : SepConvexOn (Set.Icc (-1 : ℝ) 1) f) :
    ContinuousOn f (openCube m) := by
  classical
  by_cases hm0 : m = 0
  · subst hm0
    exact continuous_of_discreteTopology.continuousOn
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
  have : Nonempty (Fin m) := ⟨⟨0, hm_pos⟩⟩
  set M : ℝ := ∑ σ : Cube m, f (vertex σ)
  have hfbdd : ∀ x ∈ cube m, 0 ≤ f x ∧ f x ≤ M := fun x hx =>
    ⟨hnn x hx, sepConvex_upper_bound hnn hsep hx⟩
  intro x0 hx0
  apply ContinuousAt.continuousWithinAt
  have hx0_abs : ∀ i : Fin m, |x0 i| < 1 := fun i =>
    abs_lt.mpr (hx0 i (Set.mem_univ i))
  let r0 : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i : Fin m => |x0 i|)
  have hr0_nn : 0 ≤ r0 := le_trans (abs_nonneg (x0 ⟨0, hm_pos⟩))
    (Finset.le_sup' (fun i : Fin m => |x0 i|) (Finset.mem_univ _))
  have hr0_lt1 : r0 < 1 := (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun i _ => hx0_abs i)
  let r : ℝ := (r0 + 1) / 2
  have hr_nn : 0 ≤ r := by dsimp only [r]; linarith
  have hr_lt1 : r < 1 := by dsimp only [r]; linarith
  have hx0_lt_r : ∀ i : Fin m, |x0 i| < r := by
    intro i
    have hi : |x0 i| ≤ r0 := Finset.le_sup' (fun j : Fin m => |x0 j|) (Finset.mem_univ i)
    dsimp only [r]
    linarith
  let box : Set (Fin m → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-r) r)
  have hbox_cube : box ⊆ cube m := by
    intro x hx
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have hi := (hx i (Set.mem_univ i)).1
      simp only [Pi.neg_apply, Pi.one_apply]
      linarith
    · have hi := (hx i (Set.mem_univ i)).2
      simp only [Pi.one_apply]
      linarith
  have hlip_box : ∀ x ∈ box, ∀ y ∈ box,
      |f y - f x| ≤ M / (1 - r) * ∑ i : Fin m, |y i - x i| := by
    intro x hx y hy
    have hS : ∀ S : Finset (Fin m),
        |f (fun i => if i ∈ S then y i else x i) - f x| ≤
          M / (1 - r) * ∑ i ∈ S, |y i - x i| := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | @insert j S hjS ih =>
        let w : Fin m → ℝ := fun i => if i ∈ S then y i else x i
        have hw_box : w ∈ box := by
          intro i hi
          simp only [w]
          split_ifs
          · exact hy i hi
          · exact hx i hi
        have hw_Icc : ∀ i, w i ∈ Set.Icc (-1 : ℝ) 1 := by
          intro i
          have hc := hbox_cube hw_box
          exact ⟨hc.1 i, hc.2 i⟩
        have hupd_y : (fun i => if i ∈ insert j S then y i else x i) =
            Function.update w j (y j) := by
          ext i; by_cases hij : i = j
          · subst hij; simp
          · simp [w, hij]
        have hupd_x : Function.update w j (x j) = w := by
          ext i; by_cases hij : i = j
          · subst hij; simp [w, hjS]
          · simp [hij]
        have hφ_bdd : ∀ u ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f (Function.update w j u) ∧
            f (Function.update w j u) ≤ M := by
          intro u hu
          apply hfbdd
          refine ⟨fun i => ?_, fun i => ?_⟩
          · by_cases hij : i = j
            · subst hij; simp [hu.1]
            · simp [hij, (hw_Icc i).1]
          · by_cases hij : i = j
            · subst hij; simp [hu.2]
            · simp [hij, (hw_Icc i).2]
        have h1d := convex_Icc_lipschitz hr_lt1 (hsep w hw_Icc j) hφ_bdd
          (hy j (Set.mem_univ j)) (hx j (Set.mem_univ j))
        rw [hupd_x] at h1d
        calc |f (fun i => if i ∈ insert j S then y i else x i) - f x|
            = |f (Function.update w j (y j)) - f x| := by rw [hupd_y]
          _ ≤ |f (Function.update w j (y j)) - f w| + |f w - f x| := abs_sub_le _ _ _
          _ ≤ M / (1 - r) * |y j - x j| + M / (1 - r) * ∑ i ∈ S, |y i - x i| := add_le_add h1d ih
          _ = M / (1 - r) * ∑ i ∈ insert j S, |y i - x i| := by
                rw [Finset.sum_insert hjS]; ring
    simpa using hS Finset.univ
  let openBox : Set (Fin m → ℝ) := Set.pi Set.univ (fun _ => Set.Ioo (-r) r)
  have hopenBox_open : IsOpen openBox := isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hx0_openBox : x0 ∈ openBox := fun i _ => abs_lt.mp (hx0_lt_r i)
  have hopenBox_sub : openBox ⊆ box := fun y hy i hi =>
    ⟨(hy i hi).1.le, (hy i hi).2.le⟩
  have hbox_nhds : box ∈ nhds x0 :=
    Filter.mem_of_superset (hopenBox_open.mem_nhds hx0_openBox) hopenBox_sub
  rw [Metric.continuousAt_iff]
  intro ε hε
  set L : ℝ := max 1 (M / (1 - r) * m)
  have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨δ1, hδ1_pos, hδ1_box⟩ := Metric.mem_nhds_iff.mp hbox_nhds
  refine ⟨min δ1 (ε / (2 * L)), lt_min hδ1_pos (by positivity), ?_⟩
  intro y hy
  have hy_box : y ∈ box := hδ1_box (lt_of_lt_of_le hy (min_le_left _ _))
  have hx0_box : x0 ∈ box := mem_of_mem_nhds hbox_nhds
  have hy_eps : dist y x0 < ε / (2 * L) := lt_of_lt_of_le hy (min_le_right _ _)
  have hsum_dist : ∑ i : Fin m, |y i - x0 i| ≤ m * dist y x0 := by
    calc ∑ i : Fin m, |y i - x0 i|
        ≤ ∑ _ : Fin m, dist y x0 :=
          Finset.sum_le_sum (fun i _ => dist_le_pi_dist y x0 i)
      _ = m * dist y x0 := by simp
  have hM_nn : 0 ≤ M :=
    (hfbdd x0 (hbox_cube hx0_box)).1.trans (hfbdd x0 (hbox_cube hx0_box)).2
  have hMr_nn : 0 ≤ M / (1 - r) := div_nonneg hM_nn (by linarith)
  rw [Real.dist_eq]
  calc |f y - f x0|
      ≤ M / (1 - r) * ∑ i : Fin m, |y i - x0 i| := hlip_box x0 hx0_box y hy_box
    _ ≤ M / (1 - r) * (m * dist y x0) := mul_le_mul_of_nonneg_left hsum_dist hMr_nn
    _ = (M / (1 - r) * m) * dist y x0 := by ring
    _ ≤ L * dist y x0 := mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg
    _ < L * (ε / (2 * L)) := mul_lt_mul_of_pos_left hy_eps hL_pos
    _ = ε / 2 := by field_simp [hL_pos.ne']
    _ < ε := by linarith

/-! ### Measure preservation of sign-flip maps on `Fin m → ℝ` -/

def mulSign {m : ℕ} (σ : Cube m) (x : Fin m → ℝ) : Fin m → ℝ :=
  fun i => vertex σ i * x i

lemma mulSign_involutive {m : ℕ} (σ : Cube m) : Function.Involutive (mulSign σ) := by
  intro x
  ext i
  simp only [mulSign, vertex, ← mul_assoc, unit_cast_sq, one_mul]

def mulSign_measurableEquiv {m : ℕ} (σ : Cube m) : (Fin m → ℝ) ≃ᵐ (Fin m → ℝ) where
  toEquiv := (mulSign_involutive σ).toPerm
  measurable_toFun := continuous_pi (fun i => continuous_const.mul (continuous_apply i)) |>.measurable
  measurable_invFun := continuous_pi (fun i => continuous_const.mul (continuous_apply i)) |>.measurable

lemma measurePreserving_mulUnit (u : ℤˣ) :
    MeasurePreserving (fun t : ℝ => ((u : ℤ) : ℝ) * t) volume volume := by
  rcases unit_cast_cases u with h1 | hm1
  · have : (fun t : ℝ => ((u : ℤ) : ℝ) * t) = id := by ext t; simp [h1]
    rw [this]
    exact MeasurePreserving.id volume
  · have : (fun t : ℝ => ((u : ℤ) : ℝ) * t) = Neg.neg := by ext t; simp [hm1]
    rw [this]
    exact Measure.measurePreserving_neg volume

lemma measurePreserving_mulSign : ∀ {m : ℕ} (σ : Cube m),
    MeasurePreserving (mulSign σ) volume volume
  | 0, σ => by
    have : mulSign σ = id := by ext x i; exact Fin.elim0 i
    rw [this]
    exact MeasurePreserving.id volume
  | m + 1, σ => by
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    have hmp_e : MeasurePreserving e volume volume :=
      MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    have hmp_e_symm : MeasurePreserving e.symm volume volume := hmp_e.symm
    let g1 : ℝ → ℝ := fun t => ((σ 0 : ℤ) : ℝ) * t
    let g2 : (Fin m → ℝ) → (Fin m → ℝ) := mulSign (fun i => σ i.succ)
    have hmp_prod : MeasurePreserving (Prod.map g1 g2) (volume.prod volume) (volume.prod volume) :=
      (measurePreserving_mulUnit (σ 0)).prod (measurePreserving_mulSign (fun i => σ i.succ))
    have hvol_prod : (volume : Measure (ℝ × (Fin m → ℝ))) = volume.prod volume :=
      Measure.volume_eq_prod ℝ (Fin m → ℝ)
    have hmp_mid : MeasurePreserving (Prod.map g1 g2) volume volume := by
      rwa [hvol_prod]
    have hcomp : mulSign σ = e.symm ∘ Prod.map g1 g2 ∘ e := by
      ext x i
      refine Fin.cases ?_ ?_ i
      · simp [e, g1, g2, mulSign, vertex]
      · intro j
        simp [e, g1, g2, mulSign, vertex, Fin.tail]
    rw [hcomp]
    exact hmp_e_symm.comp (hmp_mid.comp hmp_e)

lemma volume_posCube (m : ℕ) : volume (posCube m) = 1 := by
  unfold posCube
  rw [MeasureTheory.volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

end AuxCor19

theorem solution {m : ℕ} {n : ℝ} (hn : 0 ≤ n) (f : (Fin m → ℝ) → ℝ) (hnn : ∀ x ∈ cube m, 0 ≤ f x)
    (hsep : SepConvexOn (Set.Icc (-1 : ℝ) 1) f)
    (hhom : ∀ x ∈ cube m, ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → f (ρ • x) = ρ ^ n * f x)
    (hpos : ∀ x ∈ cube m, (∀ i, x i < 0) → 0 < f x) :
    Real.exp (-2 * n) ≤ cubeProb m {x | 0 < f x} := by
  by_cases hm0 : m = 0
  · subst hm0
    have h0_mem : (0 : Fin 0 → ℝ) ∈ cube 0 := ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    have hf0_pos : 0 < f 0 := hpos 0 h0_mem (fun i => Fin.elim0 i)
    have huniv : {x : Fin 0 → ℝ | 0 < f x} ∩ cube 0 = Set.univ := by
      ext x
      have hx0 : x = 0 := Subsingleton.elim x 0
      rw [hx0]
      simp only [Set.mem_inter_iff, Set.mem_ofPred, Set.mem_univ, iff_true]
      exact ⟨hf0_pos, h0_mem⟩
    unfold cubeProb
    rw [huniv]
    have hvol0 : volume (Set.univ : Set (Fin 0 → ℝ)) = 1 := by
      rw [← AuxCor19.volume_posCube 0]
      congr 1
      ext x; simp [AuxCor19.posCube]
    rw [hvol0]
    simp only [ENNReal.toReal_one, pow_zero, div_one]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hcont := AuxCor19.sepConvex_continuousOn_openCube hnn hsep
  have hopen_oc : IsOpen (AuxCor19.openCube m) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  let U : Set (Fin m → ℝ) := AuxCor19.openCube m ∩ {x | 0 < f x}
  have hU_open : IsOpen U := hcont.isOpen_inter_preimage hopen_oc isOpen_Ioi
  have hU_sub : U ⊆ {x | 0 < f x} ∩ cube m := by
    intro x ⟨hx_oc, hfx⟩
    refine ⟨hfx, fun i => (hx_oc i (Set.mem_univ i)).1.le, fun i => (hx_oc i (Set.mem_univ i)).2.le⟩
  have hcube_vol : volume (cube m) = (2 : ENNReal) ^ m := by
    have hc : cube m = Set.pi Set.univ (fun _ : Fin m => Set.Icc (-1 : ℝ) 1) := by
      ext x; simp [cube, Set.mem_Icc, Pi.le_def]
    rw [hc, MeasureTheory.volume_pi, Measure.pi_pi]
    simp [Real.volume_Icc, show (1 : ℝ) - -1 = 2 by ring]
  have hEc_fin : volume ({x | 0 < f x} ∩ cube m) ≠ ⊤ := by
    refine ((measure_mono Set.inter_subset_right).trans_lt ?_).ne
    rw [hcube_vol]; finiteness
  have hU_le_Ec : (volume U).toReal ≤ (volume ({x | 0 < f x} ∩ cube m)).toReal :=
    ENNReal.toReal_mono hEc_fin (measure_mono hU_sub)
  let O : Cube m → Set (Fin m → ℝ) := fun σ => AuxCor19.mulSign σ ⁻¹' AuxCor19.posCube m
  have hO_open : ∀ σ : Cube m, IsOpen (O σ) := fun σ =>
    (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)).preimage
      (continuous_pi (fun i => continuous_const.mul (continuous_apply i)))
  have hO_sub_oc : ∀ σ : Cube m, O σ ⊆ AuxCor19.openCube m := by
    intro σ x hx i _
    have hi := hx i (Set.mem_univ i)
    simp only [AuxCor19.mulSign] at hi
    rcases AuxCor19.unit_cast_cases (σ i) with h1 | hm1
    · simp only [vertex, h1, one_mul] at hi
      exact ⟨by linarith [hi.1], hi.2⟩
    · simp only [vertex, hm1, neg_mul, one_mul] at hi
      exact ⟨by linarith [hi.2], by linarith [hi.1]⟩
  have hUO_disj : Pairwise (fun σ1 σ2 : Cube m => Disjoint (U ∩ O σ1) (U ∩ O σ2)) := by
    intro σ1 σ2 hne
    rw [Set.disjoint_left]
    intro x ⟨_, hx1⟩ ⟨_, hx2⟩
    apply hne
    ext i
    by_contra hi_ne
    have hne_u : σ1 i ≠ σ2 i := fun h => hi_ne (congrArg Units.val h)
    have h1 := hx1 i (Set.mem_univ i)
    have h2 := hx2 i (Set.mem_univ i)
    simp only [AuxCor19.mulSign] at h1 h2
    rcases Int.units_eq_one_or (σ1 i) with hs1 | hs1 <;>
      rcases Int.units_eq_one_or (σ2 i) with hs2 | hs2
    · exact hne_u (hs1.trans hs2.symm)
    · simp only [vertex, hs1, hs2, Units.val_one, Int.cast_one, Units.val_neg, Int.cast_neg,
        one_mul, neg_mul] at h1 h2
      linarith [h1.1, h2.1]
    · simp only [vertex, hs1, hs2, Units.val_one, Int.cast_one, Units.val_neg, Int.cast_neg,
        one_mul, neg_mul] at h1 h2
      linarith [h1.1, h2.1]
    · exact hne_u (hs1.trans hs2.symm)
  have hUO_meas : ∀ σ : Cube m, MeasurableSet (U ∩ O σ) := fun σ =>
    (hU_open.inter (hO_open σ)).measurableSet
  have hbiUnion_sub : (⋃ σ ∈ (Finset.univ : Finset (Cube m)), (U ∩ O σ)) ⊆ U := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨σ, _, hxU, _⟩ := hx
    exact hxU
  have hU_fin : volume U ≠ ⊤ :=
    ((measure_mono hU_sub).trans_lt (lt_top_iff_ne_top.mpr hEc_fin)).ne
  have hvol_sum_le : ∑ σ : Cube m, (volume (U ∩ O σ)).toReal ≤ (volume U).toReal := by
    have h_eq : volume (⋃ σ ∈ (Finset.univ : Finset (Cube m)), (U ∩ O σ)) =
        ∑ σ : Cube m, volume (U ∩ O σ) :=
      measure_biUnion_finset (fun σ1 _ σ2 _ hne => hUO_disj hne) (fun σ _ => hUO_meas σ)
    have h_le : ∑ σ : Cube m, volume (U ∩ O σ) ≤ volume U := by
      rw [← h_eq]
      exact measure_mono hbiUnion_sub
    have h_each_fin : ∀ σ ∈ (Finset.univ : Finset (Cube m)), volume (U ∩ O σ) ≠ ⊤ := fun σ _ =>
      ((measure_mono Set.inter_subset_left).trans_lt (lt_top_iff_ne_top.mpr hU_fin)).ne
    rw [← ENNReal.toReal_sum h_each_fin]
    exact ENNReal.toReal_mono hU_fin h_le
  let E_pos : Cube m → Set (Fin m → ℝ) := fun σ =>
    AuxCor19.posCube m ∩ {s | 0 < f (AuxCor19.mulSign σ s)}
  have hUO_pre : ∀ σ : Cube m, AuxCor19.mulSign σ ⁻¹' (E_pos σ) = U ∩ O σ := by
    intro σ
    ext x
    simp only [Set.mem_preimage, E_pos, Set.mem_inter_iff, Set.mem_ofPred, U, O,
      AuxCor19.mulSign_involutive σ x]
    constructor
    · rintro ⟨hxO, hfx⟩
      exact ⟨⟨hO_sub_oc σ hxO, hfx⟩, hxO⟩
    · rintro ⟨⟨_, hfx⟩, hxO⟩
      exact ⟨hxO, hfx⟩
  have hE_pos_meas : ∀ σ : Cube m, MeasurableSet (E_pos σ) := by
    intro σ
    have hinv : E_pos σ = AuxCor19.mulSign σ ⁻¹' (U ∩ O σ) := by
      rw [← hUO_pre σ]
      ext s
      simp [AuxCor19.mulSign_involutive σ s]
    rw [hinv]
    exact (continuous_pi (fun i => continuous_const.mul (continuous_apply i))).measurable (hUO_meas σ)
  have hvol_eq : ∀ σ : Cube m, volume (U ∩ O σ) = volume (E_pos σ) := by
    intro σ
    rw [← hUO_pre σ]
    exact (AuxCor19.measurePreserving_mulSign σ).measure_preimage (hE_pos_meas σ).nullMeasurableSet
  simp_rw [hvol_eq] at hvol_sum_le
  classical
  have hpos_meas : MeasurableSet (AuxCor19.posCube m) :=
    (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)).measurableSet
  have hpos_fin : volume (AuxCor19.posCube m) ≠ ⊤ := by
    rw [AuxCor19.volume_posCube m]; exact ENNReal.one_ne_top
  let ind : Cube m → (Fin m → ℝ) → ℝ := fun σ =>
    (E_pos σ).indicator (fun _ => (1 : ℝ))
  have hind_int : ∀ σ : Cube m, IntegrableOn (ind σ) (AuxCor19.posCube m) volume := by
    intro σ
    have hE_fin : volume (E_pos σ) ≠ ⊤ :=
      ((measure_mono Set.inter_subset_left).trans_lt (lt_top_iff_ne_top.mpr hpos_fin)).ne
    exact ((integrableOn_const hE_fin).integrable_indicator (hE_pos_meas σ)).integrableOn
  have hind_integral : ∀ σ : Cube m,
      ∫ s in AuxCor19.posCube m, ind σ s = (volume (E_pos σ)).toReal := by
    intro σ
    simp only [ind]
    rw [setIntegral_indicator (hE_pos_meas σ),
      Set.inter_eq_self_of_subset_right Set.inter_subset_left,
      MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    rfl
  have hpt_lemma18 : ∀ s ∈ AuxCor19.posCube m,
      (2 : ℝ) ^ m * Real.exp (-2 * n) ≤ ∑ σ : Cube m, ind σ s := by
    intro s hs
    let gs : (Fin m → ℝ) → ℝ := fun y => f (fun i => y i * s i)
    have hys_cube : ∀ y ∈ cube m, (fun i => y i * s i) ∈ cube m := by
      intro y hy
      refine ⟨fun i => ?_, fun i => ?_⟩
      · have hsi : 0 < s i ∧ s i < 1 := hs i (Set.mem_univ i)
        have hy1 : -1 ≤ y i := hy.1 i
        have hy2 : y i ≤ 1 := hy.2 i
        simp only [Pi.neg_apply, Pi.one_apply]
        nlinarith
      · have hsi : 0 < s i ∧ s i < 1 := hs i (Set.mem_univ i)
        have hy1 : -1 ≤ y i := hy.1 i
        have hy2 : y i ≤ 1 := hy.2 i
        simp only [Pi.one_apply]
        nlinarith
    have hgs_nn : ∀ y ∈ cube m, 0 ≤ gs y := fun y hy => hnn _ (hys_cube y hy)
    have hgs_sep : SepConvexOn (Set.Icc (-1 : ℝ) 1) gs := by
      intro t ht j
      have ht_cube : t ∈ cube m := ⟨fun i => (ht i).1, fun i => (ht i).2⟩
      let ts : Fin m → ℝ := fun i => t i * s i
      have hts_Icc : ∀ i, ts i ∈ Set.Icc (-1 : ℝ) 1 := by
        intro i
        have hc := hys_cube t ht_cube
        exact ⟨hc.1 i, hc.2 i⟩
      have hconv_ts := hsep ts hts_Icc j
      refine ⟨convex_Icc (-1) 1, ?_⟩
      intro u hu v hv a b ha hb hab
      have hsj : 0 < s j ∧ s j < 1 := hs j (Set.mem_univ j)
      have hsu : u * s j ∈ Set.Icc (-1 : ℝ) 1 := ⟨by nlinarith [hu.1, hu.2], by nlinarith [hu.1, hu.2]⟩
      have hsv : v * s j ∈ Set.Icc (-1 : ℝ) 1 := ⟨by nlinarith [hv.1, hv.2], by nlinarith [hv.1, hv.2]⟩
      have h1 := hconv_ts.2 hsu hsv ha hb hab
      have hupd : ∀ w : ℝ, gs (Function.update t j w) = f (Function.update ts j (w * s j)) := by
        intro w
        simp only [gs]
        congr 1; ext i
        by_cases hij : i = j
        · subst hij; simp
        · simp [ts, hij]
      simp only [smul_eq_mul] at h1 ⊢
      rw [hupd (a * u + b * v), hupd u, hupd v]
      have hlin : (a * u + b * v) * s j = a * (u * s j) + b * (v * s j) := by ring
      rwa [hlin]
    have hgs_nz : ∃ y ∈ cube m, gs y ≠ 0 := by
      refine ⟨fun _ => -1, ⟨fun _ => le_rfl, fun _ => by norm_num⟩, ?_⟩
      have hneg_cube : (fun i => (-1 : ℝ) * s i) ∈ cube m :=
        hys_cube (fun _ => -1) ⟨fun _ => le_rfl, fun _ => by norm_num⟩
      have hneg_lt : ∀ i : Fin m, (-1 : ℝ) * s i < 0 := by
        intro i
        have hsi : 0 < s i ∧ s i < 1 := hs i (Set.mem_univ i)
        linarith
      exact (hpos _ hneg_cube hneg_lt).ne'
    have hgs_hom : ∀ σ : Cube m, ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
        gs (ρ • vertex σ) = ρ ^ n * gs (vertex σ) := by
      intro σ ρ hρ0 hρ1
      have hvert_cube : vertex σ ∈ cube m := by
        refine ⟨fun i => ?_, fun i => ?_⟩ <;>
        · rcases AuxCor19.unit_cast_cases (σ i) with h1 | hm1
          · simp [vertex, h1]
          · simp [vertex, hm1]
      have h1 := hhom (fun i => vertex σ i * s i) (hys_cube (vertex σ) hvert_cube) ρ hρ0 hρ1
      simp only [gs]
      have heq : (fun i => (ρ • vertex σ) i * s i) = ρ • (fun i => vertex σ i * s i) := by
        ext i; simp only [Pi.smul_apply, smul_eq_mul]; ring
      rwa [heq]
    have h18 := L1Sparsifiers.Main.lemma_18 hn gs hgs_nn hgs_sep hgs_nz hgs_hom
    unfold expect at h18
    have hsum_eq : (∑ σ : Cube m, if 0 < gs (vertex σ) then (1 : ℝ) else 0) =
        ∑ σ : Cube m, ind σ s := by
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      simp only [gs, ind, E_pos, Set.indicator_apply, Set.mem_inter_iff, hs, true_and,
        Set.mem_ofPred]
      by_cases h : 0 < f (AuxCor19.mulSign σ s)
      · have h' : 0 < f (fun i => vertex σ i * s i) := h
        simp [h, h']
      · have h' : ¬(0 < f (fun i => vertex σ i * s i)) := h
        simp [h, h']
    rw [hsum_eq] at h18
    have hmul := mul_le_mul_of_nonneg_left h18 (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ m)
    rwa [mul_inv_cancel_left₀ (by positivity)] at hmul
  have hint_sum : IntegrableOn (fun s => ∑ σ : Cube m, ind σ s) (AuxCor19.posCube m) volume :=
    integrable_finsetSum _ (fun σ _ => hind_int σ)
  have hint_le : (2 : ℝ) ^ m * Real.exp (-2 * n) ≤
      ∑ σ : Cube m, (volume (E_pos σ)).toReal := by
    calc (2 : ℝ) ^ m * Real.exp (-2 * n)
        = ∫ _ in AuxCor19.posCube m, ((2 : ℝ) ^ m * Real.exp (-2 * n)) := by
            rw [MeasureTheory.setIntegral_const, smul_eq_mul, Measure.real,
              AuxCor19.volume_posCube m, ENNReal.toReal_one, one_mul]
      _ ≤ ∫ s in AuxCor19.posCube m, (∑ σ : Cube m, ind σ s) :=
            setIntegral_mono_on (integrableOn_const hpos_fin) hint_sum hpos_meas hpt_lemma18
      _ = ∑ σ : Cube m, ∫ s in AuxCor19.posCube m, ind σ s :=
            MeasureTheory.integral_finsetSum _ (fun σ _ => hind_int σ)
      _ = ∑ σ : Cube m, (volume (E_pos σ)).toReal :=
            Finset.sum_congr rfl (fun σ _ => hind_integral σ)
  have hvol_final : (2 : ℝ) ^ m * Real.exp (-2 * n) ≤
      (volume ({x | 0 < f x} ∩ cube m)).toReal :=
    (hint_le.trans hvol_sum_le).trans hU_le_Ec
  unfold cubeProb
  exact (le_div_iff₀ (by positivity)).mpr (by linarith)
