-- Prove2me | solution 1 for KarimiPL.ProxCD.theorem_6_prox_cd_linear_rate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T15:17:06.41103+00:00
-- url     : https://prove2.me/submissions/53214c0d-3de4-4be9-8933-c08427749c7d

import Mathlib
import Definitions.Def_KarimiPL_ProxCD_sepG
import Definitions.Def_KarimiPL_ProxCD_sepDom
import Definitions.Def_KarimiPL_ProxCD_IsProxPL
import Definitions.Def_KarimiPL_ProxCD_IsProxCDRun
open scoped InnerProductSpace

set_option autoImplicit false

namespace KarimiPLProxCDSol

open KarimiPL.ProxCD

theorem dg_eq_of_step {d : ℕ} {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin d))} {α : ℝ} {x p : EuclideanSpace ℝ (Fin d)}
    (h : IsProxGradStep f g D α x p) :
    Dg f g D α x = -2 * α * (⟪gradient f x, p - x⟫_ℝ + α / 2 * ‖p - x‖ ^ 2 + g p - g x) := by
  unfold Dg
  congr 1
  apply le_antisymm
  · have hb : BddBelow (Set.range (fun y : D =>
        ⟪gradient f x, (y : EuclideanSpace ℝ (Fin d)) - x⟫_ℝ +
          α / 2 * ‖(y : EuclideanSpace ℝ (Fin d)) - x‖ ^ 2 + g y - g x)) := by
      refine ⟨⟪gradient f x, p - x⟫_ℝ + α / 2 * ‖p - x‖ ^ 2 + g p - g x, ?_⟩
      rintro _ ⟨y, rfl⟩
      exact h.2 y y.2
    exact ciInf_le hb (⟨p, h.1⟩ : D)
  · haveI : Nonempty D := ⟨⟨p, h.1⟩⟩
    exact le_ciInf (fun y => h.2 y y.2)

theorem seq_rate (G : ℕ → ℝ) (c : ℝ) (hnn : ∀ k, 0 ≤ G k)
    (hstep : ∀ k, G (k + 1) ≤ c * G k) : ∀ k, G k ≤ c ^ k * G 0 := by
  intro k
  rcases le_or_gt 0 c with hc | hc
  · induction k with
    | zero => simp
    | succ n ih =>
      calc G (n + 1) ≤ c * G n := hstep n
        _ ≤ c * (c ^ n * G 0) := mul_le_mul_of_nonneg_left ih hc
        _ = c ^ (n + 1) * G 0 := by ring
  · have h1 := hstep 0
    have h2 := hnn 1
    have h3 := hnn 0
    have h0 : G 0 = 0 := by
      apply le_antisymm _ h3
      nlinarith
    have hall : ∀ k, G k ≤ 0 := by
      intro k
      cases k with
      | zero => exact h0.le
      | succ n =>
        have := hstep n
        have := hnn n
        nlinarith
    rw [h0, mul_zero]
    exact hall k

theorem alg2 (L μ G M dR S : ℝ) (hL : 0 < L) (hd : 0 < dR)
    (h1 : μ * G ≤ 1 / 2 * (-2 * L * M)) (h2 : S ≤ dR * G + M) :
    S ≤ dR * (1 - μ / (dR * L)) * G := by
  have e : dR * (1 - μ / (dR * L)) * G = dR * G - μ / L * G := by
    field_simp
  have h3 : μ * G ≤ -M * L := by linarith
  have h4 : μ / L * G ≤ -M := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hL]
    exact h3
  rw [e]
  linarith

theorem single_coord {d : ℕ} (i j : Fin d) (t : ℝ) :
    (EuclideanSpace.single i t : EuclideanSpace ℝ (Fin d)) j = if j = i then t else 0 := by
  simp [PiLp.single_apply]

theorem sepG_single {d : ℕ} (gc : Fin d → ℝ → ℝ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d)
    (t : ℝ) : sepG gc (x + EuclideanSpace.single i t) = sepG gc x + (gc i (x i + t) - gc i (x i)) := by
  have h : sepG gc (x + EuclideanSpace.single i t) - sepG gc x = gc i (x i + t) - gc i (x i) := by
    unfold sepG
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · simp [single_coord]
    · intro j _ hj
      simp [single_coord, hj]
    · simp
  linarith

theorem coord_descent {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {gc : Fin d → ℝ → ℝ} {L : ℝ}
    (hsmooth : ∀ x y : EuclideanSpace ℝ (Fin d),
      f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) (t : ℝ) :
    f (x + EuclideanSpace.single i t) + sepG gc (x + EuclideanSpace.single i t) ≤
      f x + sepG gc x + coordModel f gc L i x t := by
  have hs := hsmooth x (x + EuclideanSpace.single i t)
  rw [add_sub_cancel_left] at hs
  have e1 : ⟪gradient f x, EuclideanSpace.single i t⟫_ℝ = t * gradient f x i := by
    rw [EuclideanSpace.inner_single_right]
    simp only [conj_trivial]
  have e2 : ‖(EuclideanSpace.single i t : EuclideanSpace ℝ (Fin d))‖ ^ 2 = t ^ 2 := by
    simp
  rw [e1, e2] at hs
  rw [sepG_single]
  unfold coordModel
  linarith

theorem bracket_eq {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (gc : Fin d → ℝ → ℝ) (L : ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 + sepG gc y - sepG gc x =
      ∑ j, coordModel f gc L j x (y j - x j) := by
  have e1 : ⟪gradient f x, y - x⟫_ℝ = ∑ j, (y j - x j) * gradient f x j := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [mul_comm]
  have e2 : ‖y - x‖ ^ 2 = ∑ j, (y j - x j) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp
  rw [e1, e2]
  unfold sepG coordModel
  simp only [add_sub_cancel, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]

theorem node_bound {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {gc : Fin d → ℝ → ℝ} {Dc : Fin d → Set ℝ} {L μ : ℝ} (hd : 0 < d) (hL : 0 < L)
    (hsmooth : ∀ x y : EuclideanSpace ℝ (Fin d),
      f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2)
    {xstar : EuclideanSpace ℝ (Fin d)}
    (hPL : IsProxPL f (sepG gc) (sepDom Dc) L μ xstar)
    {x : EuclideanSpace ℝ (Fin d)} (hxD : x ∈ sepDom Dc)
    (q : Fin d → EuclideanSpace ℝ (Fin d))
    (hq : ∀ i, IsCoordProxStep f gc Dc L i x (q i)) :
    ∑ i, (f (q i) + sepG gc (q i) - (f xstar + sepG gc xstar)) ≤
      (d : ℝ) * (1 - μ / (d * L)) * (f x + sepG gc x - (f xstar + sepG gc xstar)) := by
  choose t ht using hq
  have hcoord : ∀ i, f (q i) + sepG gc (q i) ≤ f x + sepG gc x + coordModel f gc L i x (t i) := by
    intro i
    rw [(ht i).2]
    exact coord_descent hsmooth x i (t i)
  let p : EuclideanSpace ℝ (Fin d) := x + WithLp.toLp 2 t
  have hp : ∀ j, p j = x j + t j := by
    intro j
    simp [p]
  have hpD : p ∈ sepDom Dc := by
    intro j
    rw [hp j]
    exact (ht j).1.1
  have hval : ⟪gradient f x, p - x⟫_ℝ + L / 2 * ‖p - x‖ ^ 2 + sepG gc p - sepG gc x =
      ∑ j, coordModel f gc L j x (t j) := by
    rw [bracket_eq]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hp j, add_sub_cancel_left]
  have hstep : IsProxGradStep f (sepG gc) (sepDom Dc) L x p := by
    refine ⟨hpD, fun y hy => ?_⟩
    rw [hval, bracket_eq]
    refine Finset.sum_le_sum (fun j _ => ?_)
    apply (ht j).1.2
    rw [add_sub_cancel]
    exact hy j
  have hpl := hPL.2 x hxD ⟨p, hstep⟩
  rw [dg_eq_of_step hstep, hval] at hpl
  have hsum : ∑ i, (f (q i) + sepG gc (q i) - (f xstar + sepG gc xstar)) ≤
      (d : ℝ) * (f x + sepG gc x - (f xstar + sepG gc xstar)) +
        ∑ j, coordModel f gc L j x (t j) := by
    have : ∑ i, (f (q i) + sepG gc (q i) - (f xstar + sepG gc xstar)) ≤
        ∑ i, ((f x + sepG gc x - (f xstar + sepG gc xstar)) + coordModel f gc L i x (t i)) :=
      Finset.sum_le_sum (fun i _ => by linarith [hcoord i])
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at this
    exact this
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  exact alg2 L μ _ _ _ _ hL hdR hpl hsum

end KarimiPLProxCDSol

open KarimiPL.ProxCD InnerProductSpace in
theorem solution {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {gc : Fin d → ℝ → ℝ} {Dc : Fin d → Set ℝ} {L μ : ℝ} (hd : 0 < d) (hL : 0 < L)
    (hf : Differentiable ℝ f)
    (hsmooth : ∀ x y : EuclideanSpace ℝ (Fin d),
      f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2)
    (hg : ∀ i, ConvexOn ℝ (Dc i) (gc i))
    {xstar : EuclideanSpace ℝ (Fin d)} (hxD : xstar ∈ sepDom Dc)
    (hmin : ∀ z ∈ sepDom Dc, f xstar + sepG gc xstar ≤ f z + sepG gc z)
    (hPL : IsProxPL f (sepG gc) (sepDom Dc) L μ xstar)
    {x0 : EuclideanSpace ℝ (Fin d)} (hx0 : x0 ∈ sepDom Dc)
    {x : (k : ℕ) → (Fin k → Fin d) → EuclideanSpace ℝ (Fin d)}
    (hrun : IsProxCDRun f gc Dc L x0 x) :
    ∀ k : ℕ, 1 / (d : ℝ) ^ k * ∑ s : Fin k → Fin d,
        (f (x k s) + sepG gc (x k s) - (f xstar + sepG gc xstar)) ≤
      (1 - μ / (d * L)) ^ k * (f x0 + sepG gc x0 - (f xstar + sepG gc xstar)) := by
  have hstepS : ∀ (k : ℕ) (s' : Fin k → Fin d) (i : Fin d),
      IsCoordProxStep f gc Dc L i (x k s') (x (k + 1) (Fin.snoc s' i)) := by
    intro k s' i
    have := hrun.2 k (Fin.snoc s' i)
    simpa [Fin.init_snoc, Fin.snoc_last] using this
  have hmem : ∀ (k : ℕ) (s : Fin k → Fin d), x k s ∈ sepDom Dc := by
    intro k
    induction k with
    | zero =>
      intro s
      rw [hrun.1 s]
      exact hx0
    | succ k ih =>
      intro s
      obtain ⟨t, ht, he⟩ := hrun.2 k s
      rw [he]
      intro j
      by_cases hj : j = s (Fin.last k)
      · subst hj
        simpa [KarimiPLProxCDSol.single_coord] using ht.1
      · simpa [KarimiPLProxCDSol.single_coord, hj] using ih (Fin.init s) j
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnn : ∀ k, 0 ≤ 1 / (d : ℝ) ^ k * ∑ s : Fin k → Fin d,
      (f (x k s) + sepG gc (x k s) - (f xstar + sepG gc xstar)) := by
    intro k
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro s _
    have := hmin _ (hmem k s)
    linarith
  have hstepA : ∀ k, 1 / (d : ℝ) ^ (k + 1) * ∑ s : Fin (k + 1) → Fin d,
      (f (x (k + 1) s) + sepG gc (x (k + 1) s) - (f xstar + sepG gc xstar)) ≤
      (1 - μ / (d * L)) * (1 / (d : ℝ) ^ k * ∑ s : Fin k → Fin d,
        (f (x k s) + sepG gc (x k s) - (f xstar + sepG gc xstar))) := by
    intro k
    have hsplit : ∑ s : Fin (k + 1) → Fin d,
        (f (x (k + 1) s) + sepG gc (x (k + 1) s) - (f xstar + sepG gc xstar)) =
        ∑ s' : Fin k → Fin d, ∑ i : Fin d,
          (f (x (k + 1) (Fin.snoc s' i)) + sepG gc (x (k + 1) (Fin.snoc s' i)) -
            (f xstar + sepG gc xstar)) := by
      rw [← (Fin.snocEquiv fun _ => Fin d).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
      rfl
    have hnode : ∀ s' : Fin k → Fin d, ∑ i : Fin d,
        (f (x (k + 1) (Fin.snoc s' i)) + sepG gc (x (k + 1) (Fin.snoc s' i)) -
          (f xstar + sepG gc xstar)) ≤
        (d : ℝ) * (1 - μ / (d * L)) * (f (x k s') + sepG gc (x k s') - (f xstar + sepG gc xstar)) :=
      fun s' => KarimiPLProxCDSol.node_bound hd hL hsmooth hPL (hmem k s')
        (fun i => x (k + 1) (Fin.snoc s' i)) (fun i => hstepS k s' i)
    rw [hsplit]
    calc 1 / (d : ℝ) ^ (k + 1) * ∑ s' : Fin k → Fin d, ∑ i : Fin d,
          (f (x (k + 1) (Fin.snoc s' i)) + sepG gc (x (k + 1) (Fin.snoc s' i)) -
            (f xstar + sepG gc xstar))
        ≤ 1 / (d : ℝ) ^ (k + 1) * ∑ s' : Fin k → Fin d, (d : ℝ) * (1 - μ / (d * L)) *
            (f (x k s') + sepG gc (x k s') - (f xstar + sepG gc xstar)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun s' _ => hnode s')) (by positivity)
      _ = (1 - μ / (d * L)) * (1 / (d : ℝ) ^ k * ∑ s : Fin k → Fin d,
            (f (x k s) + sepG gc (x k s) - (f xstar + sepG gc xstar))) := by
          rw [← Finset.mul_sum, pow_succ]
          field_simp
  intro k
  have key := KarimiPLProxCDSol.seq_rate
    (fun k => 1 / (d : ℝ) ^ k * ∑ s : Fin k → Fin d,
      (f (x k s) + sepG gc (x k s) - (f xstar + sepG gc xstar))) (1 - μ / (d * L)) hnn hstepA k
  have h0 : (1 / (d : ℝ) ^ 0 * ∑ s : Fin 0 → Fin d,
      (f (x 0 s) + sepG gc (x 0 s) - (f xstar + sepG gc xstar))) =
      f x0 + sepG gc x0 - (f xstar + sepG gc xstar) := by
    rw [Fintype.sum_unique, hrun.1]
    simp
  rw [h0] at key
  exact key
