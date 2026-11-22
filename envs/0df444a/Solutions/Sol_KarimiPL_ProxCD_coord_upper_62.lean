-- Prove2me | solution 1 for KarimiPL.ProxCD.coord_upper_62
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:57:55.907419+00:00
-- url     : https://prove2.me/submissions/c5c7f4c5-6271-46b8-a6e3-e4e6119b0313

import Mathlib
import Definitions.Def_KarimiPL_ProxCD_Setting
import Theorems.Thm_KarimiPL_GD_quadUpper_of_lipschitz

open InnerProductSpace KarimiPL.ProxCD

namespace TwentyAnalysis.ProxCD

lemma coord_bdd {d : ℕ} (f : KarimiPL.Rel.E d → ℝ) (gs : Fin d → ℝ → ℝ)
    (L : ℝ) (hL : 0 < L) (hgs : ∀ i, ConvexOn ℝ Set.univ (gs i))
    (x : KarimiPL.Rel.E d) (i : Fin d) :
    BddBelow (Set.range (coordModel f gs L x i)) := by
  obtain ⟨a, b, hab⟩ := ConvexOn.exists_affine_le_real isClosed_univ
    ((hgs i).continuousOn isOpen_univ).lowerSemicontinuousOn (hgs i)
  refine ⟨a * x i + b - gs i (x i) - (gradient f x i + a)^2 / (2 * L), ?_⟩
  rintro _ ⟨t, rfl⟩
  have hm := hab (x i + t) (Set.mem_univ _)
  have hquad : -(gradient f x i + a)^2 / (2 * L) ≤
      t * (gradient f x i + a) + L / 2 * t ^ 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * L)).mpr
    nlinarith [sq_nonneg (L * t + gradient f x i + a)]
  simp only [neg_div] at hquad
  unfold coordModel
  nlinarith

lemma inf_sum {d : ℕ} (hd : 0 < d) (h : Fin d → ℝ → ℝ)
    (hb : ∀ i, BddBelow (Set.range (h i))) :
    (⨅ y : Fin d → ℝ, ∑ i, h i (y i)) = ∑ i, ⨅ t, h i t := by
  classical
  have hlow : ∀ y : Fin d → ℝ, (∑ i, ⨅ t, h i t) ≤ ∑ i, h i (y i) := by
    intro y
    exact Finset.sum_le_sum (fun i _ => ciInf_le (hb i) (y i))
  have hbd : BddBelow (Set.range (fun y : Fin d → ℝ => ∑ i, h i (y i))) :=
    ⟨∑ i, ⨅ t, h i t, by rintro _ ⟨y, rfl⟩; exact hlow y⟩
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have hex : ∀ i, ∃ t, h i t < (⨅ t, h i t) + ε / d := by
      intro i
      exact exists_lt_of_ciInf_lt (lt_add_of_pos_right _ (div_pos hε hd'))
    choose y hy using hex
    calc
      (⨅ y : Fin d → ℝ, ∑ i, h i (y i)) ≤ ∑ i, h i (y i) := ciInf_le hbd y
      _ ≤ ∑ i, ((⨅ t, h i t) + ε / d) := Finset.sum_le_sum (fun i _ => (hy i).le)
      _ = (∑ i, ⨅ t, h i t) + ε := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  · exact le_ciInf hlow

lemma model_sum {d : ℕ} (f : KarimiPL.Rel.E d → ℝ) (gs : Fin d → ℝ → ℝ)
    (L : ℝ) (x y : KarimiPL.Rel.E d) :
    proxModel f (sepSum gs) x L y = ∑ i, coordModel f gs L x i (y i - x i) := by
  unfold proxModel coordModel sepSum
  rw [PiLp.inner_apply, EuclideanSpace.real_norm_sq_eq]
  simp only [PiLp.sub_apply, Pi.sub_apply, Real.inner_apply, sub_add_cancel]
  simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, mul_comm]

lemma model_inf {d : ℕ} (hd : 0 < d) (f : KarimiPL.Rel.E d → ℝ) (gs : Fin d → ℝ → ℝ)
    (L : ℝ) (hL : 0 < L) (hgs : ∀ i, ConvexOn ℝ Set.univ (gs i)) (x : KarimiPL.Rel.E d) :
    (⨅ y, proxModel f (sepSum gs) x L y) = ∑ i, ⨅ t, coordModel f gs L x i t := by
  have hsurj : Function.Surjective (fun y : KarimiPL.Rel.E d => fun i => y i - x i) := by
    intro t
    refine ⟨x + WithLp.toLp 2 t, ?_⟩
    funext i
    simp
  simp_rw [model_sum]
  rw [hsurj.iInf_comp (g := fun t : Fin d → ℝ => ∑ i, coordModel f gs L x i (t i))]
  exact inf_sum hd _ (coord_bdd f gs L hL hgs x)

lemma improvement {d : ℕ} (hd : 0 < d) (f : KarimiPL.Rel.E d → ℝ) (L : ℝ) (hL : 0 < L)
    (gs : Fin d → ℝ → ℝ) (hgs : ∀ i, ConvexOn ℝ Set.univ (gs i)) (x : KarimiPL.Rel.E d) :
    (1 / (d : ℝ)) * ∑ i, (⨅ t : ℝ, coordModel f gs L x i t) =
      -(1 / (2 * L * d)) * Dg f (sepSum gs) x L := by
  rw [Dg, model_inf hd f gs L hL hgs x]
  field_simp

lemma sep_step {d : ℕ} (gs : Fin d → ℝ → ℝ) (x : KarimiPL.Rel.E d)
    (i : Fin d) (t : ℝ) :
    sepSum gs (x + t • EuclideanSpace.single i (1 : ℝ)) - sepSum gs x =
      gs i (x i + t) - gs i (x i) := by
  classical
  unfold sepSum
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · simp [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply]
  · intro j hj hji
    simp [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, Ne.symm hji]
  · simp

lemma coord_upper {d : ℕ} (f : KarimiPL.Rel.E d → ℝ) (L : ℝ)
    (hCoord : ∀ (x : KarimiPL.Rel.E d) (i : Fin d) (t : ℝ),
      f (x + t • EuclideanSpace.single i (1 : ℝ)) ≤ f x + t * gradient f x i + L / 2 * t ^ 2)
    (gs : Fin d → ℝ → ℝ) (x : KarimiPL.Rel.E d) (i : Fin d) (t : ℝ) :
    (f (x + t • EuclideanSpace.single i (1 : ℝ)) + sepSum gs (x + t • EuclideanSpace.single i (1 : ℝ)))
      - (f x + sepSum gs x) ≤ coordModel f gs L x i t := by
  have hs := sep_step gs x i t
  have hf := hCoord x i t
  unfold coordModel
  linarith

lemma expected_descent {d : ℕ} (hd : 0 < d) (f : KarimiPL.Rel.E d → ℝ)
    (L : ℝ) (hL : 0 < L)
    (hCoord : ∀ (x : KarimiPL.Rel.E d) (i : Fin d) (t : ℝ),
      f (x + t • EuclideanSpace.single i (1 : ℝ)) ≤ f x + t * gradient f x i + L / 2 * t ^ 2)
    (gs : Fin d → ℝ → ℝ) (hgs : ∀ i, ConvexOn ℝ Set.univ (gs i))
    (sel : KarimiPL.Rel.E d → Fin d → KarimiPL.Rel.E d)
    (hsel : ∀ x i, IsProxCoordStep f gs L x i (sel x i)) (x : KarimiPL.Rel.E d) :
    (1 / (d : ℝ)) * ∑ i, (f (sel x i) + sepSum gs (sel x i)) ≤
      (f x + sepSum gs x) - 1 / (2 * L * d) * Dg f (sepSum gs) x L := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs (i : Fin d) : f (sel x i) + sepSum gs (sel x i) ≤
      f x + sepSum gs x + ⨅ t, coordModel f gs L x i t := by
    obtain ⟨t, ht, hmin⟩ := hsel x i
    have heq : (⨅ s, coordModel f gs L x i s) = coordModel f gs L x i t :=
      le_antisymm (ciInf_le (coord_bdd f gs L hL hgs x i) t) (le_ciInf hmin)
    rw [heq, ht]
    have h := coord_upper f L hCoord gs x i t
    linarith
  calc
    (1 / (d : ℝ)) * ∑ i, (f (sel x i) + sepSum gs (sel x i)) ≤
        (1 / (d : ℝ)) * ∑ i, (f x + sepSum gs x + ⨅ t, coordModel f gs L x i t) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hs i)) (by positivity)
    _ = f x + sepSum gs x + (1 / (d : ℝ)) * ∑ i, (⨅ t, coordModel f gs L x i t) := by
      rw [Finset.sum_add_distrib, mul_add]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      congr 1
      field_simp
    _ = _ := by rw [improvement hd f L hL gs hgs x]; ring

lemma coord_of_lip {d : ℕ} (f : KarimiPL.Rel.E d → ℝ)
    (hdiff : Differentiable ℝ f) (L : ℝ)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x : KarimiPL.Rel.E d) (i : Fin d) (t : ℝ) :
    f (x + t • EuclideanSpace.single i (1 : ℝ)) ≤ f x + t * gradient f x i + L / 2 * t ^ 2 := by
  have h := KarimiPL.GD.quadUpper_of_lipschitz f hdiff L hLip x
    (x + t • EuclideanSpace.single i (1 : ℝ))
  simpa [-inner_gradient_left, add_sub_cancel_left, inner_smul_right, EuclideanSpace.inner_single_right,
    norm_smul, PiLp.norm_single, Real.norm_eq_abs, sq_abs] using h

lemma contraction {d : ℕ} (hd : 0 < d) (f : KarimiPL.Rel.E d → ℝ)
    (L : ℝ) (hL : 0 < L)
    (hCoord : ∀ (x : KarimiPL.Rel.E d) (i : Fin d) (t : ℝ),
      f (x + t • EuclideanSpace.single i (1 : ℝ)) ≤ f x + t * gradient f x i + L / 2 * t ^ 2)
    (gs : Fin d → ℝ → ℝ) (hgs : ∀ i, ConvexOn ℝ Set.univ (gs i))
    (sel : KarimiPL.Rel.E d → Fin d → KarimiPL.Rel.E d)
    (hsel : ∀ x i, IsProxCoordStep f gs L x i (sel x i))
    (μ Fstar : ℝ) (hPL : ProxPL f (sepSum gs) L μ Fstar) (x : KarimiPL.Rel.E d) :
    (1 / (d : ℝ)) * ∑ i, (f (sel x i) + sepSum gs (sel x i) - Fstar) ≤
      (1 - μ / (d * L)) * (f x + sepSum gs x - Fstar) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs := expected_descent hd f L hL hCoord gs hgs sel hsel x
  have hp := mul_le_mul_of_nonneg_left (hPL x) (show 0 ≤ 1 / ((d : ℝ) * L) by positivity)
  have havg : (1 / (d : ℝ)) * ∑ i, (f (sel x i) + sepSum gs (sel x i) - Fstar) =
      (1 / (d : ℝ)) * ∑ i, (f (sel x i) + sepSum gs (sel x i)) - Fstar := by
    rw [Finset.sum_sub_distrib, mul_sub]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 1
    field_simp
  have heq : (1 / ((d : ℝ) * L)) * (1 / 2 * Dg f (sepSum gs) x L) =
      1 / (2 * L * d) * Dg f (sepSum gs) x L := by ring
  rw [heq] at hp
  rw [havg]
  calc
    (1 / (d : ℝ)) * ∑ i, (f (sel x i) + sepSum gs (sel x i)) - Fstar ≤
      f x + sepSum gs x - Fstar - (1 / ((d : ℝ) * L)) * (μ * (f x + sepSum gs x - Fstar)) := by linarith
    _ = _ := by ring


lemma sum_words_succ (k d : ℕ) (F : (Fin (k + 1) → Fin d) → ℝ) :
    ∑ w, F w = ∑ w : Fin k → Fin d, ∑ i : Fin d, F (Fin.snoc w i) := by
  classical
  symm
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv
    ((Equiv.prodComm (Fin k → Fin d) (Fin d)).trans (Fin.snocEquiv (fun _ => Fin d)))
    _ _ (fun _ => rfl)

lemma geometric (u : ℕ → ℝ) (q : ℝ) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) ≤ q * u k) : ∀ k, u k ≤ q ^ k * u 0 := by
  by_cases hq : 0 ≤ q
  · intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        u (k + 1) ≤ q * u k := hstep k
        _ ≤ q * (q ^ k * u 0) := mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (k + 1) * u 0 := by rw [pow_succ]; ring
  · have hz : ∀ k, u k = 0 := by
      intro k
      have hn := hu (k + 1)
      have hs := hstep k
      have hk := hu k
      have hq' : q < 0 := lt_of_not_ge hq
      nlinarith
    simp [hz]

lemma expected_recurrence {d : ℕ} (hd : 0 < d) (f : KarimiPL.Rel.E d → ℝ)
    (sel : KarimiPL.Rel.E d → Fin d → KarimiPL.Rel.E d) (x0 : KarimiPL.Rel.E d) (fstar q : ℝ)
    (hstep : ∀ x, (1 / (d : ℝ)) * ∑ i : Fin d, (f (sel x i) - fstar) ≤
      q * (f x - fstar)) (k : ℕ) :
    expectedGap f sel x0 fstar (k + 1) ≤ q * expectedGap f sel x0 fstar k := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold expectedGap
  rw [sum_words_succ]
  simp only [pcdRun, Fin.init_snoc, Fin.snoc_last]
  have heq : (1 / (d : ℝ) ^ (k + 1)) *
      ∑ w : Fin k → Fin d, ∑ i : Fin d,
        (f (sel (pcdRun sel x0 k w) i) - fstar) =
      (1 / (d : ℝ) ^ k) * ∑ w : Fin k → Fin d,
        ((1 / (d : ℝ)) * ∑ i : Fin d,
          (f (sel (pcdRun sel x0 k w) i) - fstar)) := by
    rw [← Finset.mul_sum, ← mul_assoc, pow_succ]
    congr 1
    field_simp
  rw [heq]
  calc
    (1 / (d : ℝ) ^ k) * ∑ w : Fin k → Fin d,
        ((1 / (d : ℝ)) * ∑ i : Fin d,
          (f (sel (pcdRun sel x0 k w) i) - fstar)) ≤
      (1 / (d : ℝ) ^ k) * ∑ w : Fin k → Fin d,
        (q * (f (pcdRun sel x0 k w) - fstar)) := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun w _ => hstep _
      · positivity
    _ = q * ((1 / (d : ℝ) ^ k) * ∑ w : Fin k → Fin d,
        (f (pcdRun sel x0 k w) - fstar)) := by rw [← Finset.mul_sum]; ring


end TwentyAnalysis.ProxCD

theorem solution {d : ℕ} (f : KarimiPL.Rel.E d → ℝ) (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hCoord : ∀ (x : KarimiPL.Rel.E d) (i : Fin d) (t : ℝ),
      f (x + t • EuclideanSpace.single i (1 : ℝ)) ≤ f x + t * gradient f x i + L / 2 * t ^ 2)
    (gs : Fin d → ℝ → ℝ) :
    ∀ (x : KarimiPL.Rel.E d) (i : Fin d) (t : ℝ),
      (f (x + t • EuclideanSpace.single i (1 : ℝ)) + sepSum gs (x + t • EuclideanSpace.single i (1 : ℝ)))
        - (f x + sepSum gs x) ≤ coordModel f gs L x i t := by
  exact TwentyAnalysis.ProxCD.coord_upper f L hCoord gs
