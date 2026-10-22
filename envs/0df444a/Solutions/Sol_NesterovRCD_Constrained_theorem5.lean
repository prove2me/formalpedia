-- Prove2me | solution 1 for NesterovRCD.Constrained.theorem5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T01:04:57.652341+00:00
-- url     : https://prove2.me/submissions/da4063ce-53ab-4225-b6cd-e08dba587188

import Mathlib
import Definitions.Def_NesterovRCD_HighProb_Basic
import Definitions.Def_NesterovRCD_Constrained_UCDM

set_option autoImplicit false

universe u

namespace P375

open NesterovRCD.Sublinear NesterovRCD.Constrained

section Exp

variable {n : ℕ}

lemma expect_succ (p : Fin n → ℝ) (k : ℕ) (F : (Fin (k + 1) → Fin n) → ℝ) :
    expect p (k + 1) F = expect p k (fun j => ∑ i, p i * F (Fin.snoc j i)) := by
  unfold expect
  rw [← (Fin.snocEquiv (fun _ => Fin n)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Fin.snocEquiv_apply, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  rw [show (Fin.snocEquiv (fun _ => Fin n)) (i, j) = Fin.snoc j i from rfl]
  ring

lemma expect_zero (p : Fin n → ℝ) (F : (Fin 0 → Fin n) → ℝ) :
    expect p 0 F = F (fun i => i.elim0) := by
  unfold expect
  rw [Fintype.sum_unique]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
  exact congrArg F (Subsingleton.elim _ _)

lemma expect_mono {p : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i) {k : ℕ} {F G : (Fin k → Fin n) → ℝ}
    (h : ∀ idx, F idx ≤ G idx) : expect p k F ≤ expect p k G := by
  unfold expect
  exact Finset.sum_le_sum (fun idx _ =>
    mul_le_mul_of_nonneg_left (h idx) (Finset.prod_nonneg (fun s _ => hp _)))

lemma expect_lin (p : Fin n → ℝ) (k : ℕ) (a b c : ℝ) (F G : (Fin k → Fin n) → ℝ) :
    expect p k (fun idx => a * F idx + b * G idx + c) =
      a * expect p k F + b * expect p k G + c * expect p k (fun _ => 1) := by
  unfold expect
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun _ _ => by ring)

lemma expect_one (hn : 0 < n) (k : ℕ) :
    expect (fun _ : Fin n => (n : ℝ)⁻¹) k (fun _ => 1) = 1 := by
  unfold expect
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_one]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi, nsmul_eq_mul]
  simp only [Fintype.card_fin, Finset.prod_const, Finset.card_univ]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  rw [← mul_pow, mul_inv_cancel₀ hn', one_pow]

lemma expect_cmul (p : Fin n → ℝ) (k : ℕ) (a : ℝ) (F : (Fin k → Fin n) → ℝ) :
    expect p k (fun idx => a * F idx) = a * expect p k F := by
  unfold expect
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun _ _ => by ring)

end Exp

section Blocks

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]

/-- squared ‖x - xs‖_1. -/
noncomputable def r2 (L : Fin n → ℝ) (xs x : Blocks E) : ℝ := ∑ j, L j * ‖x j - xs j‖ ^ 2

lemma wnorm_sq {L : Fin n → ℝ} (hLpos : ∀ i, 0 < L i) (v : Blocks E) :
    wnorm L 1 v ^ 2 = ∑ j, L j * ‖v j‖ ^ 2 := by
  unfold wnorm
  simp only [Real.rpow_one]
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun j _ => by have := hLpos j; positivity))]

lemma r2_nonneg {L : Fin n → ℝ} (hLpos : ∀ i, 0 < L i) (xs x : Blocks E) : 0 ≤ r2 L xs x :=
  Finset.sum_nonneg (fun j _ => by have := hLpos j; positivity)

lemma sum_single_sq (L : Fin n → ℝ) (i : Fin n) (h : E i) :
    ∑ j, L j * ‖(Pi.single i h : Blocks E) j‖ ^ 2 = L i * ‖h‖ ^ 2 := by
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
  simp

lemma ucdm_succ_snoc (f : Blocks E → ℝ) (L : Fin n → ℝ) (Q : ∀ i, Set (E i)) (x0 : Blocks E)
    (k : ℕ) (j : Fin k → Fin n) (i : Fin n) :
    ucdm f L Q x0 (k + 1) (Fin.snoc j i) = constrStep f L Q i (ucdm f L Q x0 k j) := by
  simp [ucdm, Fin.init_snoc, Fin.snoc_last]

lemma descent {f : Blocks E → ℝ} {L : Fin n → ℝ} (hL : CoordLipschitz f L) (x : Blocks E)
    (i : Fin n) (h : E i) :
    f (x + Pi.single i h) ≤ f x + partialGrad f x i h + L i / 2 * ‖h‖ ^ 2 := by
  have hd := hL.1
  set v : Blocks E := Pi.single i h with hv
  let φ : ℝ → ℝ := fun t =>
    f (x + t • v) - t * partialGrad f x i h - L i / 2 * t ^ 2 * ‖h‖ ^ 2
  let φ' : ℝ → ℝ := fun t =>
    fderiv ℝ f (x + t • v) v - partialGrad f x i h - L i * t * ‖h‖ ^ 2
  have hφ : ∀ t, HasDerivAt φ (φ' t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have h2 : HasDerivAt (fun t => f (x + t • v)) (fderiv ℝ f (x + t • v) v) t :=
      (hd (x + t • v)).hasFDerivAt.comp_hasDerivAt t h1
    have h3 : HasDerivAt (fun t : ℝ => t * partialGrad f x i h) (partialGrad f x i h) t := by
      simpa using (hasDerivAt_id t).mul_const (partialGrad f x i h)
    have h4 : HasDerivAt (fun t : ℝ => L i / 2 * t ^ 2 * ‖h‖ ^ 2) (L i * t * ‖h‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L i / 2)).mul_const (‖h‖ ^ 2)
      exact this.congr_deriv (by rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring)
    exact (h2.sub h3).sub h4
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope φ φ' zero_lt_one
    (fun t _ => (hφ t).continuousAt.continuousWithinAt) (fun t _ => hφ t)
  have hneg : φ' c ≤ 0 := by
    have hcv : x + c • v = x + Pi.single i (c • h) := by rw [hv, Pi.single_smul]
    have e1 : fderiv ℝ f (x + c • v) v = partialGrad f (x + Pi.single i (c • h)) i h := by
      rw [hcv]
      simp [partialGrad, hv]
    have e2 := hL.2.2 i x (c • h)
    have e3 : (partialGrad f (x + Pi.single i (c • h)) i - partialGrad f x i) h ≤
        ‖partialGrad f (x + Pi.single i (c • h)) i - partialGrad f x i‖ * ‖h‖ :=
      le_trans (le_abs_self _) (by rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _)
    rw [ContinuousLinearMap.sub_apply] at e3
    rw [norm_smul, Real.norm_of_nonneg hc.1.le] at e2
    simp only [φ']
    rw [e1]
    have hLi := hL.2.1 i
    have hh := norm_nonneg h
    have e4 : ‖partialGrad f (x + Pi.single i (c • h)) i - partialGrad f x i‖ * ‖h‖ ≤
        L i * (c * ‖h‖) * ‖h‖ := mul_le_mul_of_nonneg_right e2 hh
    nlinarith
  have : φ 1 - φ 0 ≤ 0 := by
    rw [hc'] at hneg
    simpa using hneg
  simp only [φ, one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, mul_one,
    sub_zero] at this
  norm_num at this
  linarith

lemma convex_grad {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : F → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hd : Differentiable ℝ f) (x y : F) :
    f x + fderiv ℝ f x (y - x) ≤ f y := by
  let g : ℝ → ℝ := fun t => f (x + t • (y - x))
  have hg : ConvexOn ℝ Set.univ g := by
    have := hf.comp_affineMap (AffineMap.lineMap x y)
    simp only [Set.preimage_univ] at this
    have e : g = f ∘ AffineMap.lineMap x y := by
      funext t
      simp [g, AffineMap.lineMap_apply_module', add_comm]
    rw [e]
    exact this
  have hder : HasDerivAt g (fderiv ℝ f x (y - x)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
    exact (hd x).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
  have := hg.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hder
  simp [slope_def_field, g] at this
  rw [map_sub]
  linarith

lemma blockUpdate_spec {f : Blocks E → ℝ} {L : Fin n → ℝ} (hL : CoordLipschitz f L)
    {Q : ∀ i, Set (E i)} (hQc : ∀ i, IsClosed (Q i)) (hQne : ∀ i, (Q i).Nonempty)
    (x : Blocks E) (i : Fin n) : IsBlockUpdate f L Q x i (blockUpdate f L Q x i) := by
  apply Classical.epsilon_spec (p := IsBlockUpdate f L Q x i)
  have hLi := hL.2.1 i
  set ℓ := partialGrad f x i
  set g : E i := (InnerProductSpace.toDual ℝ (E i)).symm ℓ
  set p : E i := x i - (L i)⁻¹ • g
  have key : ∀ w : E i, ℓ (w - x i) + L i / 2 * ‖w - x i‖ ^ 2 =
      L i / 2 * ‖w - p‖ ^ 2 - ‖g‖ ^ 2 / (2 * L i) := by
    intro w
    have hw' : w - p = (w - x i) + (L i)⁻¹ • g := by simp only [p]; abel
    have hℓ : ℓ (w - x i) = inner ℝ g (w - x i) := by
      simp only [g, InnerProductSpace.toDual_symm_apply]
    rw [hw', norm_add_sq_real, norm_smul, inner_smul_right, real_inner_comm, hℓ,
      Real.norm_of_nonneg (inv_nonneg.mpr hLi.le)]
    field_simp
    ring
  obtain ⟨u, hu, hdist⟩ := (hQc i).exists_infDist_eq_dist (hQne i) p
  refine ⟨u, hu, fun w hw => ?_⟩
  have h1 : dist p u ≤ dist p w := hdist ▸ Metric.infDist_le_dist_of_mem hw
  rw [dist_comm, dist_eq_norm, dist_comm, dist_eq_norm] at h1
  have h2 : ‖u - p‖ ^ 2 ≤ ‖w - p‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [key u, key w]
  have : L i / 2 * ‖u - p‖ ^ 2 ≤ L i / 2 * ‖w - p‖ ^ 2 :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith

lemma vi_aux {A B : ℝ} (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ t * A + t ^ 2 * B) (hB : 0 ≤ B) :
    0 ≤ A := by
  by_contra hA
  push_neg at hA
  set s := -A + 2 * B with hs
  have hspos : 0 < s := by linarith
  set t := -A / s with ht
  have htpos : 0 < t := div_pos (by linarith) hspos
  have hts : t * s = -A := by rw [ht]; field_simp
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hspos]; linarith
  have := h t htpos ht1
  have e : t * A + t ^ 2 * B = t * A / 2 * (1 + t) := by
    have : 2 * B = s + A := by rw [hs]; ring
    nlinarith
  rw [e] at this
  have : t * A < 0 := mul_neg_of_pos_of_neg htpos hA
  nlinarith

lemma blockUpdate_vi {f : Blocks E → ℝ} {L : Fin n → ℝ} (hL : CoordLipschitz f L)
    {Q : ∀ i, Set (E i)} (hQv : ∀ i, Convex ℝ (Q i)) (x : Blocks E) (i : Fin n) (u : E i)
    (hu : IsBlockUpdate f L Q x i u) (w : E i) (hw : w ∈ Q i) :
    0 ≤ partialGrad f x i (w - u) + L i * inner ℝ (u - x i) (w - u) := by
  have hLi := hL.2.1 i
  apply vi_aux (B := L i / 2 * ‖w - u‖ ^ 2) _ (by positivity)
  intro t ht0 ht1
  have hz : u + t • (w - u) ∈ Q i := (hQv i).add_smul_sub_mem hu.1 hw ⟨ht0.le, ht1⟩
  have hle := hu.2 _ hz
  have e1 : u + t • (w - u) - x i = (u - x i) + t • (w - u) := by abel
  rw [e1, map_add, map_smul, smul_eq_mul, norm_add_sq_real, norm_smul, inner_smul_right,
    Real.norm_of_nonneg ht0.le] at hle
  nlinarith

lemma constrStep_eq (f : Blocks E → ℝ) (L : Fin n → ℝ) (Q : ∀ i, Set (E i)) (i : Fin n)
    (x : Blocks E) : constrStep f L Q i x = Function.update x i (blockUpdate f L Q x i) := by
  ext j
  by_cases h : j = i
  · subst h
    simp [constrStep]
  · simp [constrStep, h, Pi.single_eq_of_ne h]

lemma step_mem {f : Blocks E → ℝ} {L : Fin n → ℝ} (hL : CoordLipschitz f L)
    {Q : ∀ i, Set (E i)} (hQc : ∀ i, IsClosed (Q i)) (hQne : ∀ i, (Q i).Nonempty)
    (x : Blocks E) (hx : x ∈ Qset Q) (i : Fin n) : constrStep f L Q i x ∈ Qset Q := by
  unfold Qset at hx ⊢
  rw [Set.mem_univ_pi] at hx ⊢
  intro j
  rw [constrStep_eq]
  by_cases h : j = i
  · subst h
    simpa using (blockUpdate_spec hL hQc hQne x j).1
  · rw [Function.update_of_ne h]
    exact hx j

lemma iter_mem {f : Blocks E → ℝ} {L : Fin n → ℝ} (hL : CoordLipschitz f L)
    {Q : ∀ i, Set (E i)} (hQc : ∀ i, IsClosed (Q i)) (hQne : ∀ i, (Q i).Nonempty)
    {x0 : Blocks E} (hx0 : x0 ∈ Qset Q) :
    ∀ k (idx : Fin k → Fin n), ucdm f L Q x0 k idx ∈ Qset Q := by
  intro k
  induction k with
  | zero => intro idx; exact hx0
  | succ k ih =>
    intro idx
    exact step_mem hL hQc hQne _ (ih _) _

lemma r2_update (L : Fin n → ℝ) (xs x : Blocks E) (i : Fin n) (u : E i) :
    r2 L xs (Function.update x i u) =
      r2 L xs x + L i * (‖u - xs i‖ ^ 2 - ‖x i - xs i‖ ^ 2) := by
  unfold r2
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have : ∑ j ∈ Finset.univ.erase i, L j * ‖Function.update x i u j - xs j‖ ^ 2 =
      ∑ j ∈ Finset.univ.erase i, L j * ‖x j - xs j‖ ^ 2 :=
    Finset.sum_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  rw [this, Function.update_self]
  ring

lemma core {f : Blocks E → ℝ} {L : Fin n → ℝ} (hL : CoordLipschitz f L)
    {Q : ∀ i, Set (E i)} (hQc : ∀ i, IsClosed (Q i)) (hQv : ∀ i, Convex ℝ (Q i))
    (hQne : ∀ i, (Q i).Nonempty) {xs : Blocks E} (hxsQ : xs ∈ Qset Q)
    (x : Blocks E) (hx : x ∈ Qset Q) (i : Fin n) :
    f (constrStep f L Q i x) ≤ f x ∧
    r2 L xs (constrStep f L Q i x) + 2 * f (constrStep f L Q i x) ≤
      r2 L xs x + 2 * f x + 2 * partialGrad f x i (xs i - x i) := by
  have hLi := hL.2.1 i
  set u := blockUpdate f L Q x i with hudef
  have hu := blockUpdate_spec hL hQc hQne x i
  rw [← hudef] at hu
  have hstep : constrStep f L Q i x = x + Pi.single i (u - x i) := rfl
  have hdesc := descent hL x i (u - x i)
  rw [← hstep] at hdesc
  unfold Qset at hx hxsQ
  rw [Set.mem_univ_pi] at hx hxsQ
  have hfeas := hu.2 (x i) (hx i)
  rw [sub_self, map_zero, norm_zero] at hfeas
  refine ⟨by linarith, ?_⟩
  have hvi := blockUpdate_vi hL hQv x i u hu (xs i) (hxsQ i)
  have hid : ‖x i - xs i‖ ^ 2 = ‖u - x i‖ ^ 2 + 2 * inner ℝ (u - x i) (xs i - u) +
      ‖u - xs i‖ ^ 2 := by
    have e : x i - xs i = -((u - x i) + (xs i - u)) := by abel
    have e' : u - xs i = -(xs i - u) := by abel
    rw [e, norm_neg, norm_add_sq_real, e', norm_neg]
  have hidL : L i * ‖x i - xs i‖ ^ 2 = L i * ‖u - x i‖ ^ 2 +
      2 * (L i * inner ℝ (u - x i) (xs i - u)) + L i * ‖u - xs i‖ ^ 2 := by
    rw [hid]; ring
  have hℓ : partialGrad f x i (xs i - u) = partialGrad f x i (xs i - x i) -
      partialGrad f x i (u - x i) := by
    rw [← map_sub]; congr 1; abel
  rw [constrStep_eq, r2_update, ← constrStep_eq]
  rw [hℓ] at hvi
  nlinarith

lemma sigma_le_one {f : Blocks E → ℝ} {L : Fin n → ℝ} (hn : 0 < n) [∀ i, Nontrivial (E i)]
    (hL : CoordLipschitz f L) {σ : ℝ} (hσ : NesterovRCD.HighProb.StronglyConvexW f L 1 σ) :
    σ ≤ 1 := by
  let i : Fin n := ⟨0, hn⟩
  obtain ⟨h, hh⟩ := exists_ne (0 : E i)
  have h1 := hσ.2 0 (0 + Pi.single i h)
  have h2 := descent hL 0 i h
  have hw : wnorm L 1 (0 + Pi.single i h - 0) ^ 2 = L i * ‖h‖ ^ 2 := by
    rw [wnorm_sq hL.2.1, zero_add, sub_zero]
    exact sum_single_sq L i h
  have he : fderiv ℝ f 0 (0 + Pi.single i h - 0) = partialGrad f 0 i h := by
    simp [partialGrad]
  rw [hw, he] at h1
  have hpos : 0 < L i * ‖h‖ ^ 2 := by
    have := hL.2.1 i
    have : 0 < ‖h‖ := norm_pos_iff.mpr hh
    positivity
  nlinarith

lemma opt_nonneg {f : Blocks E → ℝ} (hd : Differentiable ℝ f) {Q : ∀ i, Set (E i)}
    (hQv : ∀ i, Convex ℝ (Q i)) {xs : Blocks E} (hxs : IsMinimizerOn f Q xs)
    (x : Blocks E) (hx : x ∈ Qset Q) : 0 ≤ fderiv ℝ f xs (x - xs) := by
  have hconv : Convex ℝ (Qset Q) := convex_pi (fun i _ => hQv i)
  have hmin : IsMinOn f (Qset Q) xs := isMinOn_iff.mpr (fun y hy => hxs.2 y hy)
  exact hmin.localize.hasFDerivWithinAt_nonneg (hd xs).hasFDerivAt.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset (hconv.segment_subset hxs.1 hx))

end Blocks

lemma expect_add_smul {n : ℕ} (p : Fin n → ℝ) (k : ℕ) (b : ℝ) (F G : (Fin k → Fin n) → ℝ) :
    expect p k (fun idx => F idx + b * G idx) = expect p k F + b * expect p k G := by
  unfold expect
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun _ _ => by ring)

lemma expect_add_smul_const {n : ℕ} (hn : 0 < n) (k : ℕ) (b c : ℝ) (F G : (Fin k → Fin n) → ℝ) :
    expect (fun _ => (n : ℝ)⁻¹) k (fun idx => F idx + b * G idx + c) =
      expect (fun _ => (n : ℝ)⁻¹) k F + b * expect (fun _ => (n : ℝ)⁻¹) k G + c := by
  have := expect_lin (fun _ => (n : ℝ)⁻¹) k 1 b c F G
  simp only [one_mul] at this
  rw [this, expect_one hn, mul_one]

lemma sum_unif {n : ℕ} (hn : 0 < n) (c : ℝ) : ∑ _i : Fin n, (n : ℝ)⁻¹ * c = c := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_mul]

section Main

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]

lemma wnorm_r2 {L : Fin n → ℝ} (hLpos : ∀ i, 0 < L i) (xs x : Blocks E) :
    wnorm L 1 (x - xs) ^ 2 = r2 L xs x ∧ wnorm L 1 (xs - x) ^ 2 = r2 L xs x := by
  refine ⟨?_, ?_⟩
  · rw [wnorm_sq hLpos]; rfl
  · rw [wnorm_sq hLpos]; unfold r2
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Pi.sub_apply, norm_sub_rev]

lemma expect_step_le {f : Blocks E → ℝ} {L : Fin n → ℝ} (hL : CoordLipschitz f L)
    {Q : ∀ i, Set (E i)} (hQc : ∀ i, IsClosed (Q i)) (hQne : ∀ i, (Q i).Nonempty)
    {x0 : Blocks E} (hx0 : x0 ∈ Qset Q) (G H : Blocks E → ℝ)
    (hGH : ∀ x ∈ Qset Q, ∑ i, (n : ℝ)⁻¹ * G (constrStep f L Q i x) ≤ H x) (k : ℕ) :
    expect (fun _ => (n : ℝ)⁻¹) (k + 1) (fun idx => G (ucdm f L Q x0 (k + 1) idx)) ≤
      expect (fun _ => (n : ℝ)⁻¹) k (fun idx => H (ucdm f L Q x0 k idx)) := by
  rw [expect_succ]
  simp only [ucdm_succ_snoc]
  exact expect_mono (fun _ => by positivity) (fun idx => hGH _ (iter_mem hL hQc hQne hx0 k idx))

lemma S1 {f : Blocks E → ℝ} {L : Fin n → ℝ} (hn : 0 < n) (hL : CoordLipschitz f L)
    {Q : ∀ i, Set (E i)} (hQc : ∀ i, IsClosed (Q i)) (hQv : ∀ i, Convex ℝ (Q i))
    (hQne : ∀ i, (Q i).Nonempty) {xs : Blocks E} (hxsQ : xs ∈ Qset Q)
    (x : Blocks E) (hx : x ∈ Qset Q) :
    ∑ i, (n : ℝ)⁻¹ * f (constrStep f L Q i x) ≤ f x := by
  calc _ ≤ ∑ _i : Fin n, (n : ℝ)⁻¹ * f x := Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (core hL hQc hQv hQne hxsQ x hx i).1 (by positivity))
    _ = f x := sum_unif hn _

lemma S2 {f : Blocks E → ℝ} {L : Fin n → ℝ} (hn : 0 < n) (hL : CoordLipschitz f L)
    {Q : ∀ i, Set (E i)} (hQc : ∀ i, IsClosed (Q i)) (hQv : ∀ i, Convex ℝ (Q i))
    (hQne : ∀ i, (Q i).Nonempty) {xs : Blocks E} (hxsQ : xs ∈ Qset Q)
    (x : Blocks E) (hx : x ∈ Qset Q) :
    ∑ i, (n : ℝ)⁻¹ * (r2 L xs (constrStep f L Q i x) + 2 * f (constrStep f L Q i x)) ≤
      r2 L xs x + 2 * f x + 2 * (n : ℝ)⁻¹ * fderiv ℝ f x (xs - x) := by
  set A := r2 L xs x + 2 * f x with hA
  have hs : ∑ i, partialGrad f x i (xs i - x i) = fderiv ℝ f x (xs - x) :=
    ContinuousLinearMap.sum_comp_single ℝ E (fderiv ℝ f x) (xs - x)
  calc _ ≤ ∑ i, (n : ℝ)⁻¹ * (A + 2 * partialGrad f x i (xs i - x i)) :=
        Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (core hL hQc hQv hQne hxsQ x hx i).2 (by positivity))
    _ = ∑ i, ((n : ℝ)⁻¹ * A + 2 * (n : ℝ)⁻¹ * partialGrad f x i (xs i - x i)) :=
        Finset.sum_congr rfl (fun i _ => by ring)
    _ = A + 2 * (n : ℝ)⁻¹ * fderiv ℝ f x (xs - x) := by
        rw [Finset.sum_add_distrib, sum_unif hn, ← Finset.mul_sum, hs]

theorem main (hn : 0 < n) (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hL : NesterovRCD.Sublinear.CoordLipschitz f L)
    (Q : ∀ i, Set (E i)) (hQc : ∀ i, IsClosed (Q i)) (hQv : ∀ i, Convex ℝ (Q i))
    (hQne : ∀ i, (Q i).Nonempty) [∀ i, Nontrivial (E i)]
    (x0 : NesterovRCD.Sublinear.Blocks E) (hx0 : x0 ∈ Qset Q) (xs : NesterovRCD.Sublinear.Blocks E) (hxs : IsMinimizerOn f Q xs)
    (R : ℝ) (hR : LevelRadiusOnLE f L Q x0 R) :
    (∀ k : ℕ, NesterovRCD.Sublinear.expect (fun _ => (n : ℝ)⁻¹) k (fun idx => f (ucdm f L Q x0 k idx)) - f xs
        ≤ (n : ℝ) / ((n : ℝ) + k) * (R ^ 2 / 2 + f x0 - f xs)) ∧
    (∀ σ : ℝ, 0 < σ → NesterovRCD.HighProb.StronglyConvexW f L 1 σ → ∀ k : ℕ,
        NesterovRCD.Sublinear.expect (fun _ => (n : ℝ)⁻¹) k (fun idx => f (ucdm f L Q x0 k idx)) - f xs
          ≤ (1 - 2 * σ / ((n : ℝ) * (1 + σ))) ^ k * (R ^ 2 / 2 + f x0 - f xs)) := by
  have hd := hL.1
  have hLpos := hL.2.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hu0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hnR
  have hun : (n : ℝ)⁻¹ * n = 1 := inv_mul_cancel₀ hnR.ne'
  have hun1 : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hn)
  have hxsQ := hxs.1
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℝ, ∀ k, F k =
      expect (fun _ => (n : ℝ)⁻¹) k (fun idx => f (ucdm f L Q x0 k idx)) := ⟨_, fun _ => rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℕ → ℝ, ∀ k, P k =
      expect (fun _ => (n : ℝ)⁻¹) k (fun idx => r2 L xs (ucdm f L Q x0 k idx)) :=
    ⟨_, fun _ => rfl⟩
  have hF0 : F 0 = f x0 := by rw [hF, expect_zero]; rfl
  have hP0 : P 0 = r2 L xs x0 := by rw [hP, expect_zero]; rfl
  have hr0 : r2 L xs x0 ≤ R ^ 2 := by
    have h := hR x0 hx0 le_rfl xs hxs
    rw [← (wnorm_r2 hLpos xs x0).1]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  have hPnn : ∀ k, 0 ≤ P k := by
    intro k
    rw [hP]
    calc (0 : ℝ) = expect (fun _ => (n : ℝ)⁻¹) k (fun _ => 0) := by simp [expect]
      _ ≤ _ := expect_mono (fun _ => hu0.le) (fun idx => r2_nonneg hLpos _ _)
  have hFmono : ∀ k, F (k + 1) ≤ F k := by
    intro k
    rw [hF, hF]
    exact expect_step_le hL hQc hQne hx0 f f
      (fun x hx => S1 hn hL hQc hQv hQne hxsQ x hx) k
  refine ⟨?_, ?_⟩
  · have hPF : ∀ k, P (k + 1) + 2 * F (k + 1) ≤
        P k + 2 * F k + 2 * (n : ℝ)⁻¹ * (f xs - F k) := by
      intro k
      calc P (k + 1) + 2 * F (k + 1) = expect (fun _ => (n : ℝ)⁻¹) (k + 1)
            (fun idx => r2 L xs (ucdm f L Q x0 (k + 1) idx) + 2 * f (ucdm f L Q x0 (k + 1) idx)) := by
            rw [expect_add_smul, hP, hF]
        _ ≤ expect (fun _ => (n : ℝ)⁻¹) k
            (fun idx => r2 L xs (ucdm f L Q x0 k idx) + (2 - 2 * (n : ℝ)⁻¹) *
              f (ucdm f L Q x0 k idx) + 2 * (n : ℝ)⁻¹ * f xs) :=
            expect_step_le hL hQc hQne hx0 (fun x => r2 L xs x + 2 * f x)
              (fun x => r2 L xs x + (2 - 2 * (n : ℝ)⁻¹) * f x + 2 * (n : ℝ)⁻¹ * f xs)
              (fun x hx => by
                have h1 := S2 hn hL hQc hQv hQne hxsQ x hx
                have h2 := convex_grad hf hd x xs
                have h3 : 2 * (n : ℝ)⁻¹ * fderiv ℝ f x (xs - x) ≤ 2 * (n : ℝ)⁻¹ * (f xs - f x) :=
                  mul_le_mul_of_nonneg_left (by linarith) (by positivity)
                linarith) k
        _ = P k + 2 * F k + 2 * (n : ℝ)⁻¹ * (f xs - F k) := by
            rw [expect_add_smul_const hn, hP k, hF k]
            ring
    have claim : ∀ k : ℕ, P k + 2 * (F k - f xs) + 2 * (k : ℝ) * (n : ℝ)⁻¹ * (F k - f xs) ≤
        P 0 + 2 * (F 0 - f xs) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have h1 := hPF k
        have h2 := hFmono k
        have h3 : ((k : ℝ) + 1) * (n : ℝ)⁻¹ * (F (k + 1) - f xs) ≤
            ((k : ℝ) + 1) * (n : ℝ)⁻¹ * (F k - f xs) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        push_cast
        linarith
    intro k
    rw [← hF k]
    have c := claim k
    have hPk := hPnn k
    have key : (1 + (k : ℝ) * (n : ℝ)⁻¹) * (F k - f xs) ≤ R ^ 2 / 2 + f x0 - f xs := by
      rw [hP0, hF0] at c
      linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have h4 := mul_le_mul_of_nonneg_left key hnR.le
    have e : (n : ℝ) * ((1 + (k : ℝ) * (n : ℝ)⁻¹) * (F k - f xs)) = (F k - f xs) * (n + k) := by
      linear_combination ((k : ℝ) * (F k - f xs)) * hun
    linarith
  · intro σ hσ0 hσ k
    have hσ1 := sigma_le_one hn hL hσ
    set γ := 2 * σ / (1 + σ) with hγ
    have hc_eq : 2 * σ / ((n : ℝ) * (1 + σ)) = (n : ℝ)⁻¹ * γ := by
      rw [hγ]
      field_simp
    have hγ1 : γ ≤ 1 := by
      rw [hγ, div_le_one (by linarith)]
      linarith
    have hγ0 : 0 ≤ γ := by rw [hγ]; positivity
    rw [hc_eq]
    have hc0 : 0 ≤ 1 - (n : ℝ)⁻¹ * γ := by nlinarith
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℕ → ℝ, ∀ k, Φ k = expect (fun _ => (n : ℝ)⁻¹) k
        (fun idx => r2 L xs (ucdm f L Q x0 k idx) + 2 * f (ucdm f L Q x0 k idx) + (-2 * f xs)) :=
      ⟨_, fun _ => rfl⟩
    have hΦPF : ∀ k, Φ k = P k + 2 * F k + (-2 * f xs) := by
      intro k
      rw [hΦ, expect_add_smul_const hn, hP, hF]
    have hstep : ∀ k, Φ (k + 1) ≤ (1 - (n : ℝ)⁻¹ * γ) * Φ k := by
      intro k
      rw [hΦ, hΦ, ← expect_cmul]
      refine expect_step_le hL hQc hQne hx0
        (fun x => r2 L xs x + 2 * f x + (-2 * f xs))
        (fun x => (1 - (n : ℝ)⁻¹ * γ) * (r2 L xs x + 2 * f x + (-2 * f xs))) ?_ k
      intro x hx
      have h1 := S2 hn hL hQc hQv hQne hxsQ x hx
      have hsum : ∑ i, (n : ℝ)⁻¹ * (r2 L xs (constrStep f L Q i x) +
            2 * f (constrStep f L Q i x) + (-2 * f xs)) =
          ∑ i, (n : ℝ)⁻¹ * (r2 L xs (constrStep f L Q i x) + 2 * f (constrStep f L Q i x)) +
            (-2 * f xs) := by
        calc _ = ∑ i, ((n : ℝ)⁻¹ * (r2 L xs (constrStep f L Q i x) + 2 * f (constrStep f L Q i x)) +
                (n : ℝ)⁻¹ * (-2 * f xs)) := Finset.sum_congr rfl (fun i _ => by ring)
          _ = _ := by rw [Finset.sum_add_distrib, sum_unif hn]
      rw [hsum]
      have hsc1 := hσ.2 x xs
      have hsc2 := hσ.2 xs x
      rw [(wnorm_r2 hLpos xs x).2] at hsc1
      rw [(wnorm_r2 hLpos xs x).1] at hsc2
      have hopt := opt_nonneg hd hQv hxs x hx
      have hρ := r2_nonneg hLpos xs x
      set ρ := r2 L xs x
      set D := fderiv ℝ f x (xs - x)
      have ha : σ / 2 * ρ ≤ f x - f xs := by linarith
      have hgam : γ * (ρ + 2 * (f x - f xs)) ≤ 2 * (f x - f xs) + σ * ρ := by
        rw [hγ, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - σ) (by linarith : (0 : ℝ) ≤ 2 * (f x - f xs) - σ * ρ)]
      have h4 := mul_le_mul_of_nonneg_left hgam hu0.le
      have h5 : 2 * (n : ℝ)⁻¹ * D ≤ 2 * (n : ℝ)⁻¹ * (f xs - f x - σ / 2 * ρ) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have hΦk : ∀ k, Φ k ≤ (1 - (n : ℝ)⁻¹ * γ) ^ k * Φ 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc Φ (k + 1) ≤ (1 - (n : ℝ)⁻¹ * γ) * Φ k := hstep k
          _ ≤ (1 - (n : ℝ)⁻¹ * γ) * ((1 - (n : ℝ)⁻¹ * γ) ^ k * Φ 0) :=
              mul_le_mul_of_nonneg_left ih hc0
          _ = _ := by ring
    rw [← hF k]
    have h1 := hΦk k
    rw [hΦPF, hΦPF, hP0, hF0] at h1
    have hPk := hPnn k
    have hck := pow_nonneg hc0 k
    have h2 : (1 - (n : ℝ)⁻¹ * γ) ^ k * (r2 L xs x0 + 2 * f x0 + -2 * f xs) ≤
        (1 - (n : ℝ)⁻¹ * γ) ^ k * (R ^ 2 + 2 * f x0 + -2 * f xs) :=
      mul_le_mul_of_nonneg_left (by linarith) hck
    linarith

end Main

end P375

open NesterovRCD.Constrained in
theorem solution {n : ℕ} {E : Fin n → Type u} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] (hn : 0 < n) (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hL : NesterovRCD.Sublinear.CoordLipschitz f L)
    (Q : ∀ i, Set (E i)) (hQc : ∀ i, IsClosed (Q i)) (hQv : ∀ i, Convex ℝ (Q i))
    (hQne : ∀ i, (Q i).Nonempty) [∀ i, Nontrivial (E i)]
    (x0 : NesterovRCD.Sublinear.Blocks E) (hx0 : x0 ∈ Qset Q) (xs : NesterovRCD.Sublinear.Blocks E) (hxs : IsMinimizerOn f Q xs)
    (R : ℝ) (hR : LevelRadiusOnLE f L Q x0 R) :
    (∀ k : ℕ, NesterovRCD.Sublinear.expect (fun _ => (n : ℝ)⁻¹) k (fun idx => f (ucdm f L Q x0 k idx)) - f xs
        ≤ (n : ℝ) / ((n : ℝ) + k) * (R ^ 2 / 2 + f x0 - f xs)) ∧
    (∀ σ : ℝ, 0 < σ → NesterovRCD.HighProb.StronglyConvexW f L 1 σ → ∀ k : ℕ,
        NesterovRCD.Sublinear.expect (fun _ => (n : ℝ)⁻¹) k (fun idx => f (ucdm f L Q x0 k idx)) - f xs
          ≤ (1 - 2 * σ / ((n : ℝ) * (1 + σ))) ^ k * (R ^ 2 / 2 + f x0 - f xs)) := by
  exact P375.main hn f L hf hL Q hQc hQv hQne x0 hx0 xs hxs R hR
