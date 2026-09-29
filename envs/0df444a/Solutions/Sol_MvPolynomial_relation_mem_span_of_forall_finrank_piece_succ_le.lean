-- Prove2me | solution 1 for MvPolynomial.relation_mem_span_of_forall_finrank_piece_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/87cc51c5-b6a0-50e1-8812-92fa54b2b537

import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow
import Theorems.Thm_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le
import Theorems.Thm_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow
import Theorems.Thm_MvPolynomial_finrank_piece_succ_le_macaulayPow
import Theorems.Thm_MvPolynomial_exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le

set_option autoImplicit false

namespace LinSyzCore

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {σ τ ι : Type} [Fintype ι]

theorem decompose_eq (q : MvPolynomial σ K) (d : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule σ K) q d : MvPolynomial σ K) = homogeneousComponent d q :=
  MvPolynomial.decomposition.decompose'_apply q d

theorem hc_mul_left_of_le {a b : MvPolynomial σ K} {i d : ℕ} (ha : a.IsHomogeneous i) (h : i ≤ d) :
    homogeneousComponent d (a * b) = a * homogeneousComponent (d - i) b := by
  have := DirectSum.coe_decompose_mul_of_left_mem_of_le (𝒜 := homogeneousSubmodule σ K) (b := b)
    (show a ∈ homogeneousSubmodule σ K i from ha) h
  rwa [decompose_eq, decompose_eq] at this

theorem hc_mul_left_of_not_le {a b : MvPolynomial σ K} {i d : ℕ} (ha : a.IsHomogeneous i) (h : ¬i ≤ d) :
    homogeneousComponent d (a * b) = 0 := by
  have := DirectSum.coe_decompose_mul_of_left_mem_of_not_le (𝒜 := homogeneousSubmodule σ K) (b := b)
    (show a ∈ homogeneousSubmodule σ K i from ha) h
  rwa [decompose_eq] at this

theorem hc_mul_right_of_le {a b : MvPolynomial σ K} {i d : ℕ} (hb : b.IsHomogeneous i) (h : i ≤ d) :
    homogeneousComponent d (a * b) = homogeneousComponent (d - i) a * b := by
  have := DirectSum.coe_decompose_mul_of_right_mem_of_le (𝒜 := homogeneousSubmodule σ K) (a := a)
    (show b ∈ homogeneousSubmodule σ K i from hb) h
  rwa [decompose_eq, decompose_eq] at this

theorem hc_of_isHomogeneous_self {p : MvPolynomial σ K} {d : ℕ} (hp : p.IsHomogeneous d) :
    homogeneousComponent d p = p := by
  rw [homogeneousComponent_of_mem (show p ∈ homogeneousSubmodule σ K d from hp), if_pos rfl]

theorem hc_of_isHomogeneous_ne {p : MvPolynomial σ K} {d e : ℕ} (hp : p.IsHomogeneous e) (h : d ≠ e) :
    homogeneousComponent d p = 0 := by
  rw [homogeneousComponent_of_mem (show p ∈ homogeneousSubmodule σ K e from hp), if_neg h]

theorem map_homogeneousComponent (φ : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)
    (hφh : ∀ (d : ℕ) (p : MvPolynomial σ K), p.IsHomogeneous d → (φ p).IsHomogeneous d)
    (d : ℕ) (p : MvPolynomial σ K) :
    homogeneousComponent d (φ p) = φ (homogeneousComponent d p) := by
  conv_lhs => rw [← sum_homogeneousComponent p, map_sum, map_sum]
  rw [Finset.sum_eq_single d]
  · exact hc_of_isHomogeneous_self (hφh d _ (homogeneousComponent_isHomogeneous d p))
  · intro e _ hed
    exact hc_of_isHomogeneous_ne (hφh e _ (homogeneousComponent_isHomogeneous e p)) (Ne.symm hed)
  · intro hd
    have : p.totalDegree < d := by
      simp only [Finset.mem_range, not_lt] at hd
      omega
    rw [homogeneousComponent_eq_zero _ _ this, map_zero, map_zero]

noncomputable def hcv (d : ℕ) (v : ι → MvPolynomial σ K) : ι → MvPolynomial σ K :=
  fun i => homogeneousComponent d (v i)

def genSet (F : ι → MvPolynomial σ K) : Set (ι → MvPolynomial σ K) :=
  {l | (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i = 0}

noncomputable def V (F : ι → MvPolynomial σ K) : Submodule (MvPolynomial σ K) (ι → MvPolynomial σ K) :=
  Submodule.span (MvPolynomial σ K) (genSet F)

theorem rel_of_mem_V {F : ι → MvPolynomial σ K} {v : ι → MvPolynomial σ K} (hv : v ∈ V F) :
    ∑ i, v i * F i = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact hx.2
  | zero => simp
  | add x y _ _ hx hy =>
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hx, hy, add_zero]
  | smul a x _ hx =>
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hx, mul_zero]

theorem hcv_mem {F : ι → MvPolynomial σ K} {v : ι → MvPolynomial σ K} (hv : v ∈ V F) (d : ℕ) :
    hcv d v ∈ V F := by
  induction hv using Submodule.span_induction generalizing d with
  | mem l hl =>
      obtain ⟨d', _, hl'⟩ := hl.1
      by_cases h : d = d'
      · subst h
        have : hcv d l = l := funext fun i => hc_of_isHomogeneous_self (hl' i)
        rw [this]; exact Submodule.subset_span hl
      · have : hcv d l = 0 := funext fun i => hc_of_isHomogeneous_ne (hl' i) h
        rw [this]; exact zero_mem _
  | zero =>
      have : hcv d (0 : ι → MvPolynomial σ K) = 0 := funext fun i => by simp [hcv]
      rw [this]; exact zero_mem _
  | add x y _ _ hx hy =>
      have : hcv d (x + y) = hcv d x + hcv d y := funext fun i => by simp [hcv]
      rw [this]; exact add_mem (hx d) (hy d)
  | smul p v _ ih =>
      have hp : p = ∑ e ∈ Finset.range (p.totalDegree + 1), homogeneousComponent e p :=
        (sum_homogeneousComponent p).symm
      have hsplit : hcv d (p • v) =
          ∑ e ∈ Finset.range (p.totalDegree + 1), hcv d (homogeneousComponent e p • v) := by
        funext i
        simp only [hcv, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
        conv_lhs => rw [hp, Finset.sum_mul]
        rw [map_sum]
      rw [hsplit]
      refine Submodule.sum_mem _ fun e _ => ?_
      by_cases hed : e ≤ d
      · have h2 : hcv d (homogeneousComponent e p • v) = homogeneousComponent e p • hcv (d - e) v := by
          funext i
          simp only [hcv, Pi.smul_apply, smul_eq_mul]
          exact hc_mul_left_of_le (homogeneousComponent_isHomogeneous e p) hed
        rw [h2]; exact Submodule.smul_mem _ _ (ih (d - e))
      · have h2 : hcv d (homogeneousComponent e p • v) = 0 := by
          funext i
          simp only [hcv, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
          exact hc_mul_left_of_not_le (homogeneousComponent_isHomogeneous e p) hed
        rw [h2]; exact zero_mem _

theorem sub_C_coeff_zero_mem (a : MvPolynomial τ K) :
    a - C (coeff 0 a) ∈ Ideal.span (Set.range (X : τ → MvPolynomial τ K)) := by
  classical
  rw [← Set.image_univ, mem_ideal_span_X_image]
  intro mono hmono
  have hne : mono ≠ 0 := by
    rintro rfl
    rw [mem_support_iff, coeff_sub, coeff_zero_C, sub_self] at hmono
    exact hmono rfl
  obtain ⟨i, hi⟩ : ∃ i, mono i ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (Finsupp.ext h)
  exact ⟨i, Set.mem_univ i, hi⟩

section Core

variable (φ : MvPolynomial σ K →ₐ[K] MvPolynomial τ K) (ψ : MvPolynomial τ K →ₐ[K] MvPolynomial σ K)
  (hφψ : ∀ p, φ (ψ p) = p)
  (ℓ : MvPolynomial σ K) (hℓ : ℓ.IsHomogeneous 1) (hℓ0 : ℓ ≠ 0) (hφℓ : φ ℓ = 0)
  (hker : ∀ p, φ p = 0 → ∃ q, p = ℓ * q)
  (hφh : ∀ (d : ℕ) (p : MvPolynomial σ K), p.IsHomogeneous d → (φ p).IsHomogeneous d)
  (hψh : ∀ (d : ℕ) (p : MvPolynomial τ K), p.IsHomogeneous d → (ψ p).IsHomogeneous d)
  {m : ℕ} (F : ι → MvPolynomial σ K) (hF : ∀ i, (F i).IsHomogeneous m)
  (hcol : ∀ f : MvPolynomial σ K, f.IsHomogeneous m →
    ℓ * f ∈ Ideal.span (Set.range F) → f ∈ Ideal.span (Set.range F))

include hφψ hℓ hφℓ hker hψh hF hcol in

theorem lift_linear_relation (r' : ι → MvPolynomial τ K) (hr'1 : ∀ i, (r' i).IsHomogeneous 1)
    (hr'rel : ∑ i, r' i * φ (F i) = 0) :
    ∃ r : ι → MvPolynomial σ K, r ∈ genSet F ∧ (∀ i, (r i).IsHomogeneous 1) ∧ ∀ i, φ (r i) = r' i := by
  classical
  obtain ⟨R, hR⟩ : ∃ R : MvPolynomial σ K, R = ∑ i, ψ (r' i) * F i := ⟨_, rfl⟩
  have hRJ : R ∈ Ideal.span (Set.range F) :=
    hR ▸ Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have hRh : R.IsHomogeneous (1 + m) :=
    hR ▸ IsHomogeneous.sum _ _ _ fun i _ => (hψh 1 _ (hr'1 i)).mul (hF i)
  have hφR : φ R = 0 := by
    rw [hR, map_sum]
    simp only [map_mul, hφψ]
    exact hr'rel
  obtain ⟨q, hq⟩ := hker R hφR
  obtain ⟨G, hG⟩ : ∃ G : MvPolynomial σ K, G = homogeneousComponent m q := ⟨_, rfl⟩
  have hGh : G.IsHomogeneous m := hG ▸ homogeneousComponent_isHomogeneous m q
  have hRG : R = ℓ * G := by
    rw [← hc_of_isHomogeneous_self hRh, hq, hc_mul_left_of_le hℓ (Nat.le_add_right 1 m),
      Nat.add_sub_cancel_left, hG]
  have hGJ : G ∈ Ideal.span (Set.range F) := hcol G hGh (by rw [← hRG]; exact hRJ)
  obtain ⟨p, hp⟩ := Ideal.mem_span_range_iff_exists_fun.mp hGJ

  have hGsum : G = ∑ i, C (coeff 0 (p i)) * F i := by
    rw [← hc_of_isHomogeneous_self hGh, ← hp, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc_mul_right_of_le (hF i) le_rfl, Nat.sub_self, homogeneousComponent_zero]
  have hhom : ∀ i, (ψ (r' i) - C (coeff 0 (p i)) * ℓ).IsHomogeneous 1 := fun i =>
    (hψh 1 _ (hr'1 i)).sub (by simpa using (isHomogeneous_C σ (coeff 0 (p i))).mul hℓ)
  refine ⟨fun i => ψ (r' i) - C (coeff 0 (p i)) * ℓ, ⟨⟨1, le_rfl, hhom⟩, ?_⟩, hhom, fun i => ?_⟩
  · calc ∑ i, (ψ (r' i) - C (coeff 0 (p i)) * ℓ) * F i
          = ∑ i, ψ (r' i) * F i - ℓ * ∑ i, C (coeff 0 (p i)) * F i := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [← hR, ← hGsum, hRG, sub_self]
  · simp [map_sub, map_mul, hφψ, hφℓ]

include hφψ hℓ hφℓ hker hψh hF hcol in

theorem claimA (y : ι → MvPolynomial τ K) (hy : y ∈ V (fun i => φ (F i))) :
    ∃ v ∈ V F, ∃ w : ι → K, (∑ i, C (w i) * φ (F i) = 0) ∧ ∀ i, y i = φ (v i) + C (w i) := by
  classical
  have hlift := lift_linear_relation φ ψ hφψ ℓ hℓ hφℓ hker hψh F hF hcol
  induction hy using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨⟨d', hd', hyh⟩, hyrel⟩ := hy
      interval_cases d'
      ·
        have hyC : ∀ i, y i = C (coeff 0 (y i)) := fun i => by
          rw [← homogeneousComponent_zero, hc_of_isHomogeneous_self (hyh i)]
        refine ⟨0, zero_mem _, fun i => coeff 0 (y i), ?_, fun i => ?_⟩
        · rw [← hyrel]; exact Finset.sum_congr rfl fun i _ => by rw [← hyC i]
        · rw [Pi.zero_apply, map_zero, zero_add]; exact hyC i
      ·
        obtain ⟨r, hrgen, -, hφr⟩ := hlift y hyh hyrel
        refine ⟨r, Submodule.subset_span hrgen, 0, by simp, fun i => ?_⟩
        rw [Pi.zero_apply, map_zero, add_zero, hφr]
  | zero => exact ⟨0, zero_mem _, 0, by simp, fun i => by simp⟩
  | add y z _ _ hy hz =>
      obtain ⟨v₁, hv₁, w₁, hw₁, h₁⟩ := hy
      obtain ⟨v₂, hv₂, w₂, hw₂, h₂⟩ := hz
      refine ⟨v₁ + v₂, add_mem hv₁ hv₂, w₁ + w₂, ?_, fun i => ?_⟩
      · simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, hw₁, hw₂, add_zero]
      · rw [Pi.add_apply, h₁ i, h₂ i, Pi.add_apply, Pi.add_apply, map_add, map_add]; ring
  | smul a y _ ih =>
      obtain ⟨v₀, hv₀, w₀, hw₀, h₀⟩ := ih

      have hq := sub_C_coeff_zero_mem (K := K) a
      have key : ∃ v₁ ∈ V F, ∀ i, (a - C (coeff 0 a)) * C (w₀ i) = φ (v₁ i) := by
        refine Submodule.span_induction
          (p := fun x _ => ∃ v₁ ∈ V F, ∀ i, x * C (w₀ i) = φ (v₁ i)) ?_ ?_ ?_ ?_ hq
        · intro x hx
          obtain ⟨k, rfl⟩ := hx
          have h1 : ∀ i, (X k * C (w₀ i) : MvPolynomial τ K).IsHomogeneous 1 := fun i => by
            simpa using (isHomogeneous_X K k).mul (isHomogeneous_C τ (w₀ i))
          have h2 : ∑ i, X k * C (w₀ i) * φ (F i) = 0 := by
            simp only [mul_assoc, ← Finset.mul_sum, hw₀, mul_zero]
          obtain ⟨r, hrgen, -, hφr⟩ := hlift (fun i => X k * C (w₀ i)) h1 h2
          exact ⟨r, Submodule.subset_span hrgen, fun i => (hφr i).symm⟩
        · exact ⟨0, zero_mem _, fun i => by simp⟩
        · intro x x' _ _ hx hx'
          obtain ⟨v₁, hv₁, h₁⟩ := hx
          obtain ⟨v₂, hv₂, h₂⟩ := hx'
          exact ⟨v₁ + v₂, add_mem hv₁ hv₂, fun i => by rw [add_mul, h₁ i, h₂ i, Pi.add_apply, map_add]⟩
        · intro b x _ hx
          obtain ⟨v₁, hv₁, h₁⟩ := hx
          refine ⟨ψ b • v₁, Submodule.smul_mem _ _ hv₁, fun i => ?_⟩
          rw [smul_eq_mul, mul_assoc, h₁ i, Pi.smul_apply, smul_eq_mul, map_mul, hφψ]
      obtain ⟨v₁, hv₁, hv₁eq⟩ := key
      refine ⟨ψ a • v₀ + v₁, add_mem (Submodule.smul_mem _ _ hv₀) hv₁, fun i => coeff 0 a * w₀ i, ?_, fun i => ?_⟩
      · simp only [map_mul, mul_assoc, ← Finset.mul_sum, hw₀, mul_zero]
      · rw [Pi.smul_apply, smul_eq_mul, h₀ i, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, hφψ,
          map_mul C, ← hv₁eq i]
        ring

include hφψ hℓ hℓ0 hφℓ hker hφh hψh hF hcol in

theorem core
    (hIH : ∀ (d : ℕ) (c' : ι → MvPolynomial τ K), (∀ i, (c' i).IsHomogeneous d) →
      ∑ i, c' i * φ (F i) = 0 → c' ∈ V (fun i => φ (F i)))
    (d : ℕ) (c : ι → MvPolynomial σ K) (hc : ∀ i, (c i).IsHomogeneous d) (hcF : ∑ i, c i * F i = 0) :
    c ∈ V F := by
  classical
  induction d using Nat.strong_induction_on generalizing c with
  | _ d ih =>
    rcases d with _ | d
    · exact Submodule.subset_span ⟨⟨0, zero_le_one, hc⟩, hcF⟩
    ·
      have hφc : ∀ i, (φ (c i)).IsHomogeneous (d + 1) := fun i => hφh _ _ (hc i)
      have hφrel : ∑ i, φ (c i) * φ (F i) = 0 := by
        have := congrArg φ hcF
        rwa [map_sum, map_zero, Finset.sum_congr rfl fun i _ => map_mul φ (c i) (F i)] at this
      obtain ⟨v, hv, w, -, heq⟩ :=
        claimA φ ψ hφψ ℓ hℓ hφℓ hker hψh F hF hcol _ (hIH (d + 1) (fun i => φ (c i)) hφc hφrel)
      have hv' : hcv (d + 1) v ∈ V F := hcv_mem hv (d + 1)
      have hφcv : ∀ i, φ (c i - hcv (d + 1) v i) = 0 := fun i => by
        have e2 : homogeneousComponent (d + 1) (C (w i) : MvPolynomial τ K) = 0 :=
          hc_of_isHomogeneous_ne (isHomogeneous_C τ (w i)) (Nat.succ_ne_zero d)
        rw [map_sub, ← hc_of_isHomogeneous_self (hφc i), heq i, map_add, e2, add_zero,
          map_homogeneousComponent φ hφh, sub_eq_zero]
        rfl

      choose q hq using fun i => hker _ (hφcv i)
      have hce : ∀ i, c i - hcv (d + 1) v i = ℓ * homogeneousComponent d (q i) := fun i => by
        have h1 : (c i - hcv (d + 1) v i).IsHomogeneous (d + 1) :=
          (hc i).sub (homogeneousComponent_isHomogeneous _ _)
        rw [← hc_of_isHomogeneous_self h1, hq i, hc_mul_left_of_le hℓ (Nat.le_add_left 1 d), Nat.add_sub_cancel]
      have herel : ∑ i, homogeneousComponent d (q i) * F i = 0 := by
        have h1 : ∑ i, (c i - hcv (d + 1) v i) * F i = 0 := by
          simp only [sub_mul, Finset.sum_sub_distrib, hcF, rel_of_mem_V hv', sub_self]
        have h2 : ℓ * ∑ i, homogeneousComponent d (q i) * F i = 0 := by
          rw [Finset.mul_sum, ← h1]
          exact Finset.sum_congr rfl fun i _ => by rw [hce i, mul_assoc]
        exact (mul_eq_zero.mp h2).resolve_left hℓ0
      have heV := ih d (Nat.lt_succ_self d) (fun i => homogeneousComponent d (q i))
        (fun i => homogeneousComponent_isHomogeneous _ _) herel
      have hc_eq : c = hcv (d + 1) v + ℓ • fun i => homogeneousComponent d (q i) := funext fun i => by
        rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← hce i]; ring
      rw [hc_eq]
      exact add_mem hv' (Submodule.smul_mem _ _ heV)

end Core

section Pieces

open AlgebraicGeometry.HilbertFunctor

variable {L : Type} [Field L] {n : ℕ}

noncomputable def Ik (I : Ideal (MvPolynomial (Fin (n + 1)) L)) (d : ℕ) :
    Submodule L ↥(homogeneousSubmodule (Fin (n + 1)) L d) :=
  Submodule.comap (homogeneousSubmodule (Fin (n + 1)) L d).subtype (I.restrictScalars L)

theorem mem_Ik {I : Ideal (MvPolynomial (Fin (n + 1)) L)} {d : ℕ}
    (x : ↥(homogeneousSubmodule (Fin (n + 1)) L d)) :
    x ∈ Ik I d ↔ (x : MvPolynomial (Fin (n + 1)) L) ∈ I := Iff.rfl

theorem Ik_mono {I I' : Ideal (MvPolynomial (Fin (n + 1)) L)} (h : I ≤ I') (d : ℕ) : Ik I d ≤ Ik I' d :=
  fun x hx => (mem_Ik x).mpr (h ((mem_Ik x).mp hx))

scoped instance finite_homogeneousSubmodule (d : ℕ) :
    Module.Finite L ↥(homogeneousSubmodule (Fin (n + 1)) L d) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  haveI : Finite {x : Fin (n + 1) →₀ ℕ | x.degree = d} :=
    ((Finsupp.finite_of_degree_le d).subset fun x (hx : x.degree = d) => le_of_eq hx).to_subtype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport L {x : Fin (n + 1) →₀ ℕ | x.degree = d})

scoped instance finite_piece (I : Ideal (MvPolynomial (Fin (n + 1)) L)) (d : ℕ) : Module.Finite L (piece I d) :=
  Module.Finite.quotient L _

theorem finrank_piece_add (I : Ideal (MvPolynomial (Fin (n + 1)) L)) (d : ℕ) :
    Module.finrank L (piece I d) + Module.finrank L ↥(Ik I d) =
      Module.finrank L ↥(homogeneousSubmodule (Fin (n + 1)) L d) := by
  unfold Ik; exact Submodule.finrank_quotient_add_finrank _

theorem finrank_piece_eq_zero_of_forall {I : Ideal (MvPolynomial (Fin (n + 1)) L)} {d : ℕ}
    (h : ∀ f : MvPolynomial (Fin (n + 1)) L, f.IsHomogeneous d → f ∈ I) : Module.finrank L (piece I d) = 0 := by
  have htop : Ik I d = ⊤ := eq_top_iff.mpr fun x _ => (mem_Ik x).mpr (h x x.2)
  have h1 := finrank_piece_add I d
  rw [htop, finrank_top] at h1
  omega

theorem span_homogeneous (s : Set (MvPolynomial (Fin (n + 1)) L))
    (hs : ∀ p ∈ s, ∃ i : ℕ, p.IsHomogeneous i) :
    ∀ p ∈ Ideal.span s, ∀ d : ℕ, homogeneousComponent d p ∈ Ideal.span s := by
  intro p hp d
  have H := Ideal.homogeneous_span (homogeneousSubmodule (Fin (n + 1)) L) s (fun x hx => hs x hx)
  have := H d hp
  rwa [decompose_eq] at this

theorem homogeneous_of_gen {m : ℕ} (J : Ideal (MvPolynomial (Fin (n + 1)) L))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) L), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s) :
    ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J := by
  obtain ⟨s, hs, rfl⟩ := hJ
  exact span_homogeneous s fun p hp => ⟨m, hs p hp⟩

theorem homogeneous_sup {m : ℕ} (J : Ideal (MvPolynomial (Fin (n + 1)) L))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) L), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (ℓ : MvPolynomial (Fin (n + 1)) L) (hℓ : ℓ.IsHomogeneous 1) :
    ∀ p ∈ J ⊔ Ideal.span {ℓ}, ∀ i : ℕ, homogeneousComponent i p ∈ J ⊔ Ideal.span {ℓ} := by
  obtain ⟨s, hs, rfl⟩ := hJ
  have : Ideal.span s ⊔ Ideal.span {ℓ} = Ideal.span (s ∪ {ℓ}) := (Submodule.span_union s {ℓ}).symm
  rw [this]
  refine span_homogeneous (s ∪ {ℓ}) ?_
  rintro p (hp | hp)
  · exact ⟨m, hs p hp⟩
  · exact ⟨1, by rw [Set.mem_singleton_iff.mp hp]; exact hℓ⟩

theorem finrank_piece_succ_eq_add (I : Ideal (MvPolynomial (Fin (n + 1)) L))
    (hI : ∀ p ∈ I, ∀ i : ℕ, homogeneousComponent i p ∈ I)
    (ℓ : MvPolynomial (Fin (n + 1)) L) (hℓ : ℓ.IsHomogeneous 1) (k : ℕ)
    (hcol : ∀ f : MvPolynomial (Fin (n + 1)) L, f.IsHomogeneous k → ℓ * f ∈ I → f ∈ I) :
    Module.finrank L (piece I (k + 1)) =
      Module.finrank L (piece I k) + Module.finrank L (piece (I ⊔ Ideal.span {ℓ}) (k + 1)) := by
  by_cases hℓ0 : ℓ = 0
  · subst hℓ0
    have h0 : Module.finrank L (piece I k) = 0 :=
      finrank_piece_eq_zero_of_forall fun f hf => hcol f hf (by rw [zero_mul]; exact I.zero_mem)
    have hbot : Ideal.span ({0} : Set (MvPolynomial (Fin (n + 1)) L)) = ⊥ := Ideal.span_singleton_eq_bot.mpr rfl
    rw [h0, zero_add, hbot, sup_bot_eq]
  let μ : ↥(homogeneousSubmodule (Fin (n + 1)) L k) →ₗ[L] ↥(homogeneousSubmodule (Fin (n + 1)) L (k + 1)) :=
    LinearMap.codRestrict (homogeneousSubmodule (Fin (n + 1)) L (k + 1))
      ((LinearMap.mulLeft L ℓ) ∘ₗ (homogeneousSubmodule (Fin (n + 1)) L k).subtype)
      (fun f => by
        show (ℓ * (f : MvPolynomial (Fin (n + 1)) L)).IsHomogeneous (k + 1)
        have := hℓ.mul f.2; rwa [Nat.add_comm 1 k] at this)
  have hμ : ∀ f : ↥(homogeneousSubmodule (Fin (n + 1)) L k),
      (μ f : MvPolynomial (Fin (n + 1)) L) = ℓ * f := fun f => rfl
  have hμinj : Function.Injective μ := by
    intro f g hfg
    have := congrArg Subtype.val hfg
    rw [hμ, hμ] at this
    exact Subtype.ext (mul_left_cancel₀ hℓ0 this)
  have hA1 : Ik (I ⊔ Ideal.span {ℓ}) (k + 1) = Ik I (k + 1) ⊔ LinearMap.range μ := by
    apply le_antisymm
    · intro x hx
      rw [mem_Ik] at hx
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      have hx1 : (x : MvPolynomial (Fin (n + 1)) L) = homogeneousComponent (k + 1) x :=
        (hc_of_isHomogeneous_self x.2).symm
      have hgl : homogeneousComponent (k + 1) (g * ℓ) = homogeneousComponent k g * ℓ := by
        rw [hc_mul_right_of_le hℓ (Nat.le_add_left 1 k), Nat.add_sub_cancel]
      have hyk : homogeneousComponent (k + 1) y ∈ homogeneousSubmodule (Fin (n + 1)) L (k + 1) :=
        homogeneousComponent_isHomogeneous _ _
      have hgk : homogeneousComponent k g ∈ homogeneousSubmodule (Fin (n + 1)) L k :=
        homogeneousComponent_isHomogeneous _ _
      have hxeq : (x : MvPolynomial (Fin (n + 1)) L) =
          homogeneousComponent (k + 1) y + ℓ * homogeneousComponent k g := by
        calc (x : MvPolynomial (Fin (n + 1)) L) = homogeneousComponent (k + 1) (y + g * ℓ) := by
              rw [hyz]; exact hx1
          _ = homogeneousComponent (k + 1) y + ℓ * homogeneousComponent k g := by
              rw [map_add, hgl, mul_comm ℓ]
      have hxeq' : x = ⟨homogeneousComponent (k + 1) y, hyk⟩ + μ ⟨homogeneousComponent k g, hgk⟩ := by
        apply Subtype.ext
        rw [Submodule.coe_add, hμ]
        exact hxeq
      rw [hxeq']
      exact Submodule.add_mem_sup ((mem_Ik _).mpr (hI y hy (k + 1))) (LinearMap.mem_range_self μ _)
    · apply sup_le (Ik_mono (I := I) (I' := I ⊔ Ideal.span {ℓ}) le_sup_left (k + 1))
      rintro _ ⟨f, rfl⟩
      rw [mem_Ik, hμ]
      exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ℓ))
  have hA2 : Ik I (k + 1) ⊓ LinearMap.range μ = (Ik I k).map μ := by
    apply le_antisymm
    · rintro y ⟨hyI, ⟨f, rfl⟩⟩
      have hyI' : ℓ * (f : MvPolynomial (Fin (n + 1)) L) ∈ I := by rw [← hμ]; exact (mem_Ik _).mp hyI
      have hf : f ∈ Ik I k := (mem_Ik f).mpr (hcol f f.2 hyI')
      exact Submodule.mem_map_of_mem hf
    · rintro _ ⟨f, hf, rfl⟩
      refine ⟨(mem_Ik _).mpr ?_, LinearMap.mem_range_self μ f⟩
      rw [hμ]; exact I.mul_mem_left ℓ ((mem_Ik f).mp hf)
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq (Ik I (k + 1)) (LinearMap.range μ)
  rw [← hA1, hA2, LinearMap.finrank_range_of_inj hμinj,
    (Submodule.equivMapOfInjective μ hμinj (Ik I k)).symm.finrank_eq] at e1
  have e2 := finrank_piece_add I k
  have e3 := finrank_piece_add I (k + 1)
  have e4 := finrank_piece_add (I ⊔ Ideal.span {ℓ}) (k + 1)
  omega

theorem finrank_homogeneousSubmodule (d : ℕ) :
    Module.finrank L ↥(homogeneousSubmodule (Fin (n + 1)) L d) = Nat.card {x : Fin (n + 1) →₀ ℕ // x.degree = d} := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport L {x : Fin (n + 1) →₀ ℕ | x.degree = d})

theorem finrank_homogeneousSubmodule_le (d : ℕ) :
    Module.finrank L ↥(homogeneousSubmodule (Fin (n + 1)) L d) ≤ (n + d).choose n := by
  classical
  rw [finrank_homogeneousSubmodule]
  let e : {s : Fin (n + 1) →₀ ℕ // s.degree = d} → Sym (Fin (n + 1)) d := fun s =>
    ⟨Finsupp.toMultiset s.1, by
      have h2 := s.2
      rw [Finsupp.degree_apply] at h2
      rw [Finsupp.card_toMultiset]
      simpa [Finsupp.sum] using h2⟩
  have he : Function.Injective e := by
    intro s t h
    have h1 : Finsupp.toMultiset s.1 = Finsupp.toMultiset t.1 :=
      congrArg (fun x : Sym (Fin (n + 1)) d => (x : Multiset (Fin (n + 1)))) h
    have h2 := congrArg Multiset.toFinsupp h1
    rw [Finsupp.toMultiset_toFinsupp, Finsupp.toMultiset_toFinsupp] at h2
    exact Subtype.ext h2
  haveI : Finite {s : Fin (n + 1) →₀ ℕ // s.degree = d} := Finite.of_injective e he
  have := Nat.card_le_card_of_injective e he
  rw [Nat.card_eq_fintype_card (α := Sym (Fin (n + 1)) d), Sym.card_sym_eq_choose, Fintype.card_fin,
    show n + 1 + d - 1 = n + d by omega] at this
  rw [Nat.choose_symm_add]; exact this

theorem finrank_piece_le (I : Ideal (MvPolynomial (Fin (n + 1)) L)) (d : ℕ) :
    Module.finrank L (piece I d) ≤ (n + d).choose n := by
  have := finrank_piece_add I d
  have := finrank_homogeneousSubmodule_le (n := n) (L := L) d
  omega

end Pieces

section Hyperplane

variable {n : ℕ} (a : Fin (n + 1) → K)

noncomputable def ell : MvPolynomial (Fin (n + 1)) K := ∑ i, C (a i) * X i

theorem ell_def : ell a = ∑ i, C (a i) * X i := rfl

noncomputable def gsub : Fin (n + 1) → MvPolynomial (Fin n) K :=
  Fin.lastCases (C (-(a (Fin.last n))⁻¹) * ∑ j : Fin n, C (a j.castSucc) * X j) (fun j => X j)

theorem gsub_castSucc (j : Fin n) : gsub a j.castSucc = X j := by
  simp [gsub]

theorem gsub_last : gsub a (Fin.last n) = C (-(a (Fin.last n))⁻¹) * ∑ j : Fin n, C (a j.castSucc) * X j := by
  simp [gsub]

noncomputable def phi : MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin n) K := aeval (gsub a)

noncomputable def psi : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin (n + 1)) K := rename Fin.castSucc

theorem phi_X (i : Fin (n + 1)) : phi a (X i) = gsub a i := aeval_X _ _

theorem phi_psi (p : MvPolynomial (Fin n) K) : phi a (psi p) = p := by
  unfold phi psi
  rw [aeval_rename]
  have : gsub a ∘ Fin.castSucc = X := funext (gsub_castSucc a)
  rw [this, aeval_X_left_apply]

theorem phi_surjective : Function.Surjective (phi a) := fun p => ⟨psi p, phi_psi a p⟩

theorem gsub_isHomogeneous (i : Fin (n + 1)) : (gsub a i).IsHomogeneous 1 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [gsub_last]
    simpa using (isHomogeneous_C (Fin n) (-(a (Fin.last n))⁻¹)).mul
      (IsHomogeneous.sum _ _ 1 fun j _ => isHomogeneous_C_mul_X (a j.castSucc) j)
  · rw [gsub_castSucc]; exact isHomogeneous_X K j

theorem phi_isHomogeneous (d : ℕ) (p : MvPolynomial (Fin (n + 1)) K) (hp : p.IsHomogeneous d) :
    (phi a p).IsHomogeneous d := by
  have h__af := hp.aeval (gsub a) (gsub_isHomogeneous a)
  simp at h__af
  exact h__af

theorem psi_isHomogeneous (d : ℕ) (p : MvPolynomial (Fin n) K) (hp : p.IsHomogeneous d) :
    (psi (K := K) p).IsHomogeneous d := hp.rename_isHomogeneous

theorem ell_isHomogeneous : (ell a).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X (a i) i

theorem eval_ell (x : Fin (n + 1) → K) : eval x (ell a) = ∑ i, a i * x i := by
  simp [ell, map_sum]

variable (ha : a (Fin.last n) ≠ 0)
include ha

theorem ell_ne_zero : ell a ≠ 0 := by
  intro h
  have := congrArg (eval (Pi.single (Fin.last n) (1 : K))) h
  rw [eval_ell, map_zero, Finset.sum_eq_single (Fin.last n) (fun i _ hi => by rw [Pi.single_eq_of_ne hi, mul_zero])
    (fun h => (h (Finset.mem_univ _)).elim), Pi.single_eq_same, mul_one] at this
  exact ha this

theorem phi_ell : phi a (ell a) = 0 := by
  have hC : C (a (Fin.last n)) * C (-(a (Fin.last n))⁻¹) = (-1 : MvPolynomial (Fin n) K) := by
    rw [← C_mul, mul_neg, mul_inv_cancel₀ ha, C_neg, C_1]
  rw [ell_def, map_sum]
  simp only [map_mul, algHom_C, MvPolynomial.algebraMap_eq, phi_X]
  rw [Fin.sum_univ_castSucc]
  simp only [gsub_castSucc, gsub_last]
  rw [← mul_assoc, hC]
  ring

theorem ker_phi (p : MvPolynomial (Fin (n + 1)) K) (hp : phi a p = 0) : ∃ q, p = ell a * q := by
  suffices h : ∀ p : MvPolynomial (Fin (n + 1)) K, ∃ q, p - psi (phi a p) = ell a * q by
    obtain ⟨q, hq⟩ := h p
    exact ⟨q, by rwa [hp, map_zero, sub_zero] at hq⟩
  intro p
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨0, by simp [psi, phi]⟩
  | add p q hp hq =>
      obtain ⟨r, hr⟩ := hp
      obtain ⟨s, hs⟩ := hq
      exact ⟨r + s, by rw [map_add, map_add, mul_add, ← hr, ← hs]; ring⟩
  | mul_X p i hp =>
      obtain ⟨r, hr⟩ := hp
      have hX : ∃ κ : K, X i - psi (phi a (X i)) = ell a * C κ := by
        refine Fin.lastCases ?_ (fun j => ?_) i
        · refine ⟨(a (Fin.last n))⁻¹, ?_⟩
          have hC : C (a (Fin.last n)) * C ((a (Fin.last n))⁻¹) = (1 : MvPolynomial (Fin (n + 1)) K) := by
            rw [← C_mul, mul_inv_cancel₀ ha, C_1]
          have h1 : psi (phi a (X (Fin.last n))) =
              C (-(a (Fin.last n))⁻¹) * ∑ j : Fin n, C (a j.castSucc) * X j.castSucc := by
            rw [phi_X, gsub_last]
            simp only [psi, map_mul, rename_C, map_sum, rename_X]
          rw [h1, ell_def, Fin.sum_univ_castSucc, C_neg]
          linear_combination (-(X (Fin.last n) : MvPolynomial (Fin (n + 1)) K)) * hC
        · exact ⟨0, by rw [phi_X, gsub_castSucc]; simp [psi]⟩
      obtain ⟨κ, hκ⟩ := hX
      refine ⟨r * X i + psi (phi a p) * C κ, ?_⟩
      rw [map_mul, map_mul]
      linear_combination (X i) * hr + (psi (phi a p)) * hκ

end Hyperplane

section Transport

open AlgebraicGeometry.HilbertFunctor

variable {n : ℕ} (a : Fin (n + 2) → K) (ha : a (Fin.last (n + 1)) ≠ 0)
include ha

theorem finrank_piece_transport (I : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hI : ∀ p ∈ I, ∀ i : ℕ, homogeneousComponent i p ∈ I) (k : ℕ) :
    Module.finrank K (piece (I ⊔ Ideal.span {ell a}) k) =
      Module.finrank K (piece (Ideal.map (phi a) I) k) := by
  let φk : ↥(homogeneousSubmodule (Fin (n + 2)) K k) →ₗ[K] ↥(homogeneousSubmodule (Fin (n + 1)) K k) :=
    LinearMap.codRestrict (homogeneousSubmodule (Fin (n + 1)) K k)
      ((phi a).toLinearMap ∘ₗ (homogeneousSubmodule (Fin (n + 2)) K k).subtype)
      (fun x => phi_isHomogeneous a k x x.2)
  have hφk : ∀ x : ↥(homogeneousSubmodule (Fin (n + 2)) K k), (φk x : MvPolynomial (Fin (n + 1)) K) = phi a x :=
    fun x => rfl
  let N := Submodule.comap (homogeneousSubmodule (Fin (n + 1)) K k).subtype
    ((Ideal.map (phi a) I).restrictScalars K)
  let Θ : ↥(homogeneousSubmodule (Fin (n + 2)) K k) →ₗ[K] piece (Ideal.map (phi a) I) k := N.mkQ ∘ₗ φk
  have hΘ : ∀ x, Θ x = N.mkQ (φk x) := fun x => rfl
  have hΘsurj : Function.Surjective Θ := by
    intro y
    obtain ⟨y, rfl⟩ := N.mkQ_surjective y
    refine ⟨⟨psi (K := K) y, psi_isHomogeneous k _ y.2⟩, ?_⟩
    rw [hΘ]
    congr 1
    exact Subtype.ext (phi_psi a y)
  have hker : LinearMap.ker Θ =
      Submodule.comap (homogeneousSubmodule (Fin (n + 2)) K k).subtype ((I ⊔ Ideal.span {ell a}).restrictScalars K) := by
    ext x
    rw [LinearMap.mem_ker, hΘ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change (φk x : MvPolynomial (Fin (n + 1)) K) ∈ Ideal.map (phi a) I ↔
      (x : MvPolynomial (Fin (n + 2)) K) ∈ I ⊔ Ideal.span {ell a}
    rw [hφk]
    constructor
    · intro hx
      obtain ⟨j, hj, hjx⟩ := (Ideal.mem_map_iff_of_surjective (phi a) (phi_surjective a)).mp hx
      have h1 : phi a ((x : MvPolynomial (Fin (n + 2)) K) - homogeneousComponent k j) = 0 := by
        rw [map_sub, ← map_homogeneousComponent (phi a) (phi_isHomogeneous a), hjx,
          hc_of_isHomogeneous_self (phi_isHomogeneous a k _ x.2), sub_self]
      obtain ⟨q, hq⟩ := ker_phi a ha _ h1
      have : (x : MvPolynomial (Fin (n + 2)) K) = homogeneousComponent k j + ell a * q := by
        rw [← hq]; ring
      rw [this]
      exact Submodule.add_mem_sup (hI j hj k) (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    · intro hx
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      rw [← hyz, map_add, map_mul, phi_ell a ha, mul_zero, add_zero]
      exact Ideal.mem_map_of_mem _ hy
  have e1 := LinearMap.quotKerEquivOfSurjective Θ hΘsurj
  rw [← e1.finrank_eq]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).finrank_eq

end Transport

section InfiniteField

open AlgebraicGeometry.HilbertFunctor

theorem rel_mem_V_fin_zero {g : ℕ} (F : Fin g → MvPolynomial (Fin 0) K) (d : ℕ) (c : Fin g → MvPolynomial (Fin 0) K)
    (hc : ∀ i, (c i).IsHomogeneous d) (hcF : ∑ i, c i * F i = 0) : c ∈ V F := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Submodule.subset_span ⟨⟨0, zero_le_one, hc⟩, hcF⟩
  · have : c = 0 := funext fun i => by
      ext u
      have hu : u = 0 := Finsupp.ext fun j => j.elim0
      rw [Pi.zero_apply, coeff_zero]
      exact (hc i).coeff_eq_zero (by rw [hu, map_zero]; omega)
    rw [this]; exact zero_mem _

theorem exists_eval_ne_zero [Infinite K] {n : ℕ} {G₁ G₂ : MvPolynomial (Fin (n + 1)) K} (h₁ : G₁ ≠ 0) (h₂ : G₂ ≠ 0) :
    ∃ a : Fin (n + 1) → K, MvPolynomial.eval a G₁ ≠ 0 ∧ MvPolynomial.eval a G₂ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply mul_ne_zero h₁ h₂
  apply MvPolynomial.funext
  intro a
  rw [map_mul, map_zero]
  by_cases h1 : MvPolynomial.eval a G₁ = 0
  · rw [h1, zero_mul]
  · rw [hcon a h1, mul_zero]

theorem span_range_generated {n m g : ℕ} (F : Fin g → MvPolynomial (Fin (n + 1)) K) (hF : ∀ i, (F i).IsHomogeneous m) :
    ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ Ideal.span (Set.range F) = Ideal.span s :=
  ⟨Set.range F, by rintro _ ⟨i, rfl⟩; exact hF i, rfl⟩

theorem infinite_main [Infinite K] : ∀ (n : ℕ) (m : ℕ), 1 ≤ m → ∀ (g : ℕ) (F : Fin g → MvPolynomial (Fin (n + 1)) K),
    (∀ i, (F i).IsHomogeneous m) →
    Module.finrank K (piece (Ideal.span (Set.range F)) (m + 1)) =
      Nat.macaulayPow m (Module.finrank K (piece (Ideal.span (Set.range F)) m)) →
    ∀ (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K), (∀ i, (c i).IsHomogeneous d) →
      ∑ i, c i * F i = 0 → c ∈ V F
  | 0 => by
      intro m hm g F hF hmax d c hc hcF
      obtain ⟨G₂, hG₂, H₂⟩ :=
        MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow 0 m K
          (Ideal.span (Set.range F)) (span_range_generated F hF) hmax
      obtain ⟨a, ha₂, haX⟩ := exists_eval_ne_zero hG₂ (X_ne_zero (Fin.last 0) : (X (Fin.last 0) : MvPolynomial (Fin 1) K) ≠ 0)
      have ha : a (Fin.last 0) ≠ 0 := by rwa [eval_X] at haX
      have hcol : ∀ f : MvPolynomial (Fin 1) K, f.IsHomogeneous m →
          ell a * f ∈ Ideal.span (Set.range F) → f ∈ Ideal.span (Set.range F) :=
        fun f hf h => H₂ a ha₂ m le_rfl f hf h
      exact core (phi a) psi (phi_psi a) (ell a) (ell_isHomogeneous a) (ell_ne_zero a ha) (phi_ell a ha)
        (ker_phi a ha) (phi_isHomogeneous a) (fun d p hp => psi_isHomogeneous d p hp) F hF hcol
        (fun d c' hc' hrel => rel_mem_V_fin_zero _ d c' hc' hrel) d c hc hcF
  | n + 1 => by
      intro m hm g F hF hmax d c hc hcF
      have hJgen := span_range_generated F hF
      have hJh := homogeneous_of_gen (Ideal.span (Set.range F)) hJgen
      obtain ⟨G₁, hG₁, H₁⟩ :=
        MvPolynomial.exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le (n + 1) m hm K
          (Ideal.span (Set.range F)) hJh
      obtain ⟨G₂, hG₂, H₂⟩ :=
        MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow (n + 1) m K
          (Ideal.span (Set.range F)) hJgen hmax
      obtain ⟨a, ha₁₂, haX⟩ := exists_eval_ne_zero (mul_ne_zero hG₁ hG₂)
        (X_ne_zero (Fin.last (n + 1)) : (X (Fin.last (n + 1)) : MvPolynomial (Fin (n + 2)) K) ≠ 0)
      rw [map_mul] at ha₁₂
      obtain ⟨ha₁, ha₂⟩ := mul_ne_zero_iff.mp ha₁₂
      have ha : a (Fin.last (n + 1)) ≠ 0 := by rwa [eval_X] at haX
      have hcol : ∀ f : MvPolynomial (Fin (n + 2)) K, f.IsHomogeneous m →
          ell a * f ∈ Ideal.span (Set.range F) → f ∈ Ideal.span (Set.range F) :=
        fun f hf h => H₂ a ha₂ m le_rfl f hf h

      have hA := finrank_piece_succ_eq_add (Ideal.span (Set.range F)) hJh (ell a) (ell_isHomogeneous a) m hcol
      have hrt := H₁ a ha₁
      have hmac := MvPolynomial.finrank_piece_succ_le_macaulayPow (n + 1) m hm K
        (Ideal.span (Set.range F) ⊔ Ideal.span {ell a}) (homogeneous_sup _ hJgen _ (ell_isHomogeneous a))
      rw [← ell_def] at hrt
      set s0 := Module.finrank K (piece (Ideal.span (Set.range F)) m)
      set s1 := Module.finrank K (piece (Ideal.span (Set.range F)) (m + 1))
      set t0 := Module.finrank K (piece (Ideal.span (Set.range F) ⊔ Ideal.span {ell a}) m)
      set t1 := Module.finrank K (piece (Ideal.span (Set.range F) ⊔ Ideal.span {ell a}) (m + 1))
      have ht1 : t1 = Nat.macaulayPow m t0 := by omega

      have hJbar : Ideal.map (phi a) (Ideal.span (Set.range F)) = Ideal.span (Set.range fun i => phi a (F i)) := by
        rw [Ideal.map_span, ← Set.range_comp]; rfl
      have hF' : ∀ i, (phi a (F i)).IsHomogeneous m := fun i => phi_isHomogeneous a m _ (hF i)
      have hmax' : Module.finrank K (piece (Ideal.span (Set.range fun i => phi a (F i))) (m + 1)) =
          Nat.macaulayPow m (Module.finrank K (piece (Ideal.span (Set.range fun i => phi a (F i))) m)) := by
        rw [← hJbar, ← finrank_piece_transport a ha _ hJh, ← finrank_piece_transport a ha _ hJh]
        exact ht1
      have hIH := infinite_main n m hm g (fun i => phi a (F i)) hF' hmax'
      exact core (phi a) psi (phi_psi a) (ell a) (ell_isHomogeneous a) (ell_ne_zero a ha) (phi_ell a ha)
        (ker_phi a ha) (phi_isHomogeneous a) (fun d p hp => psi_isHomogeneous d p hp) F hF hcol hIH d c hc hcF

end InfiniteField

section DegreeZero

theorem hcol_of_degree_zero {n g : ℕ} (F : Fin g → MvPolynomial (Fin (n + 1)) K) (hF : ∀ i, (F i).IsHomogeneous 0)
    (a : Fin (n + 1) → K) (ha : a (Fin.last n) ≠ 0) :
    ∀ f : MvPolynomial (Fin (n + 1)) K, f.IsHomogeneous 0 →
      ell a * f ∈ Ideal.span (Set.range F) → f ∈ Ideal.span (Set.range F) := by
  intro f _ h
  by_cases h0 : ∃ i₀, F i₀ ≠ 0
  · obtain ⟨i₀, hi₀⟩ := h0
    have hFC : F i₀ = C (coeff 0 (F i₀)) := by
      rw [← homogeneousComponent_zero, hc_of_isHomogeneous_self (hF i₀)]
    have hx : coeff 0 (F i₀) ≠ 0 := fun hx => hi₀ (by rw [hFC, hx, C_0])
    have htop : Ideal.span (Set.range F) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i₀, rfl⟩)
        (by rw [hFC]; exact (isUnit_iff_ne_zero.mpr hx).map C)
    rw [htop]; exact Submodule.mem_top
  · push Not at h0
    have hbot : Ideal.span (Set.range F) = ⊥ := by
      rw [Ideal.span_eq_bot]; rintro _ ⟨i, rfl⟩; exact h0 i
    rw [hbot, Ideal.mem_bot] at h ⊢
    exact (mul_eq_zero.mp h).resolve_left (ell_ne_zero a ha)

theorem zero_degree_main : ∀ (n g : ℕ) (F : Fin g → MvPolynomial (Fin (n + 1)) K), (∀ i, (F i).IsHomogeneous 0) →
    ∀ (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K), (∀ i, (c i).IsHomogeneous d) →
      ∑ i, c i * F i = 0 → c ∈ V F
  | 0 => by
      intro g F hF d c hc hcF
      let a : Fin 1 → K := fun _ => 1
      have ha : a (Fin.last 0) ≠ 0 := one_ne_zero
      exact core (phi a) psi (phi_psi a) (ell a) (ell_isHomogeneous a) (ell_ne_zero a ha) (phi_ell a ha)
        (ker_phi a ha) (phi_isHomogeneous a) (fun d p hp => psi_isHomogeneous d p hp) F hF
        (hcol_of_degree_zero F hF a ha)
        (fun d c' hc' hrel => rel_mem_V_fin_zero _ d c' hc' hrel) d c hc hcF
  | n + 1 => by
      intro g F hF d c hc hcF
      let a : Fin (n + 2) → K := fun _ => 1
      have ha : a (Fin.last (n + 1)) ≠ 0 := one_ne_zero
      have hF' : ∀ i, (phi a (F i)).IsHomogeneous 0 := fun i => phi_isHomogeneous a 0 _ (hF i)
      exact core (phi a) psi (phi_psi a) (ell a) (ell_isHomogeneous a) (ell_ne_zero a ha) (phi_ell a ha)
        (ker_phi a ha) (phi_isHomogeneous a) (fun d p hp => psi_isHomogeneous d p hp) F hF
        (hcol_of_degree_zero F hF a ha)
        (zero_degree_main n g (fun i => phi a (F i)) hF') d c hc hcF

end DegreeZero

section Descent

variable {σ : Type} (L : Type) [Field L] [Algebra K L]

noncomputable def Λ (f : L →ₗ[K] K) (q : MvPolynomial σ L) : MvPolynomial σ K :=
  ∑ u ∈ q.support, monomial u (f (coeff u q))

theorem coeff_Λ (f : L →ₗ[K] K) (q : MvPolynomial σ L) (u : σ →₀ ℕ) : coeff u (Λ L f q) = f (coeff u q) := by
  classical
  unfold Λ
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, map_zero]

theorem Λ_zero (f : L →ₗ[K] K) : Λ L f (0 : MvPolynomial σ L) = 0 := by
  ext u; rw [coeff_Λ, coeff_zero, coeff_zero, map_zero]

theorem Λ_add (f : L →ₗ[K] K) (q q' : MvPolynomial σ L) : Λ L f (q + q') = Λ L f q + Λ L f q' := by
  ext u; simp only [coeff_Λ, coeff_add, map_add]

theorem Λ_sum (f : L →ₗ[K] K) {α : Type} (s : Finset α) (q : α → MvPolynomial σ L) :
    Λ L f (∑ i ∈ s, q i) = ∑ i ∈ s, Λ L f (q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Λ_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Λ_add, ih]

theorem Λ_map_mul (f : L →ₗ[K] K) (p : MvPolynomial σ K) (q : MvPolynomial σ L) :
    Λ L f (map (algebraMap K L) p * q) = p * Λ L f q := by
  classical
  ext u
  rw [coeff_Λ, coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_map, coeff_Λ, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

theorem Λ_C_mul (f : L →ₗ[K] K) (x : L) (q : MvPolynomial σ L) :
    Λ L f (C x * q) = Λ L (f ∘ₗ LinearMap.mulLeft K x) q := by
  ext u; rw [coeff_Λ, coeff_Λ, coeff_C_mul]; rfl

theorem Λ_map (f : L →ₗ[K] K) (hf : f 1 = 1) (p : MvPolynomial σ K) : Λ L f (map (algebraMap K L) p) = p := by
  have h := Λ_map_mul L f p 1
  rw [mul_one] at h
  have h1 : Λ L f (1 : MvPolynomial σ L) = 1 := by
    classical
    ext u
    rw [coeff_Λ, coeff_one, coeff_one]
    split_ifs
    · exact hf
    · exact map_zero f
  rw [h, h1, mul_one]

theorem Λ_isHomogeneous (f : L →ₗ[K] K) {q : MvPolynomial σ L} {d : ℕ} (hq : q.IsHomogeneous d) :
    (Λ L f q).IsHomogeneous d := by
  intro u hu
  rw [coeff_Λ] at hu
  exact hq fun h => hu (by rw [h, map_zero])

theorem exists_functional_one : ∃ f : L →ₗ[K] K, f 1 = 1 := by
  let b := Module.Basis.ofVectorSpace K L
  have h1 : b.repr 1 ≠ 0 := by
    rw [Ne, LinearEquiv.map_eq_zero_iff]; exact one_ne_zero
  obtain ⟨β, hβ⟩ : ∃ β, b.repr 1 β ≠ 0 := by
    by_contra h
    push Not at h
    exact h1 (Finsupp.ext h)
  refine ⟨(b.repr 1 β)⁻¹ • b.coord β, ?_⟩
  rw [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul, inv_mul_cancel₀ hβ]

theorem descend {n g : ℕ} (F : Fin g → MvPolynomial (Fin (n + 1)) K)
    (hV : ∀ (d : ℕ) (c' : Fin g → MvPolynomial (Fin (n + 1)) L), (∀ i, (c' i).IsHomogeneous d) →
      ∑ i, c' i * map (algebraMap K L) (F i) = 0 → c' ∈ V (fun i => map (algebraMap K L) (F i)))
    (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K) (hc : ∀ i, (c i).IsHomogeneous d)
    (hcF : ∑ i, c i * F i = 0) : c ∈ V F := by
  classical
  obtain ⟨f, hf⟩ := exists_functional_one (K := K) L
  have key : ∀ y ∈ V (fun i => map (algebraMap K L) (F i)), ∀ f : L →ₗ[K] K,
      (fun i => Λ L f (y i)) ∈ V F := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        intro f
        obtain ⟨⟨d', hd', hyh⟩, hyrel⟩ := hy
        refine Submodule.subset_span ⟨⟨d', hd', fun i => Λ_isHomogeneous L f (hyh i)⟩, ?_⟩
        have h1 : ∑ i, Λ L f (y i) * F i = Λ L f (∑ i, map (algebraMap K L) (F i) * y i) := by
          rw [Λ_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [Λ_map_mul, mul_comm]
        have h2 : ∑ i, map (algebraMap K L) (F i) * y i = 0 := by
          rw [← hyrel]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
        rw [h1, h2, Λ_zero]
    | zero =>
        intro f
        have : (fun i => Λ L f ((0 : Fin g → MvPolynomial (Fin (n + 1)) L) i)) = 0 :=
          funext fun i => by simp [Λ_zero]
        rw [this]; exact zero_mem _
    | add y z _ _ hy hz =>
        intro f
        have : (fun i => Λ L f ((y + z) i)) = (fun i => Λ L f (y i)) + fun i => Λ L f (z i) :=
          funext fun i => by simp [Λ_add]
        rw [this]; exact add_mem (hy f) (hz f)
    | smul b y _ ih =>
        intro f
        have hb : ∀ i, Λ L f ((b • y) i) =
            ∑ u ∈ b.support, monomial u (1 : K) * Λ L (f ∘ₗ LinearMap.mulLeft K (coeff u b)) (y i) := by
          intro i
          rw [Pi.smul_apply, smul_eq_mul]
          conv_lhs => rw [b.as_sum, Finset.sum_mul]
          rw [Λ_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          have : (monomial u (coeff u b) : MvPolynomial (Fin (n + 1)) L) =
              map (algebraMap K L) (monomial u 1) * C (coeff u b) := by
            rw [map_monomial, map_one, mul_comm, C_mul_monomial, mul_one]
          rw [this, mul_assoc, Λ_map_mul, Λ_C_mul]
        have : (fun i => Λ L f ((b • y) i)) = ∑ u ∈ b.support,
            (monomial u (1 : K)) • fun i => Λ L (f ∘ₗ LinearMap.mulLeft K (coeff u b)) (y i) := by
          funext i
          rw [hb i, Finset.sum_apply]
          rfl
        rw [this]
        exact Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (ih _)
  have hmc : (fun i => map (algebraMap K L) (c i)) ∈ V (fun i => map (algebraMap K L) (F i)) := by
    refine hV d _ (fun i => (hc i).map _) ?_
    have := congrArg (map (algebraMap K L)) hcF
    rwa [map_sum, map_zero, Finset.sum_congr rfl fun i _ => map_mul _ (c i) (F i)] at this
  have h := key _ hmc f
  have hcid : (fun i => Λ L f (map (algebraMap K L) (c i))) = c := funext fun i => Λ_map L f hf (c i)
  rwa [hcid] at h

end Descent

section Assembly

open AlgebraicGeometry.HilbertFunctor

theorem finrank_piece_map {n : ℕ} (L : Type) [Field L] [Algebra K L] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J) (d : ℕ) :
    Module.finrank L (piece (J.map (MvPolynomial.map (algebraMap K L))) d) = Module.finrank K (piece J d) := by
  obtain ⟨-, h⟩ := AlgebraicGeometry.HilbertFunctor.exists_linearEquiv_baseChange_piece_map n K L J hJ
  obtain ⟨e, -⟩ := h d
  rw [← e.finrank_eq, Module.finrank_baseChange]

theorem main (n m g : ℕ) (F : Fin g → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous m)
    (hmax : ∀ J' : Ideal (MvPolynomial (Fin (n + 1)) K),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J' = Ideal.span s) →
      Module.finrank K (piece J' m) = Module.finrank K (piece (Ideal.span (Set.range F)) m) →
      Module.finrank K (piece J' (m + 1)) ≤ Module.finrank K (piece (Ideal.span (Set.range F)) (m + 1)))
    (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K) (hc : ∀ i, (c i).IsHomogeneous d)
    (hcF : ∑ i, c i * F i = 0) : c ∈ V F := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact zero_degree_main n g F hF d c hc hcF
  · have hJgen := span_range_generated F hF
    have hJh := homogeneous_of_gen (Ideal.span (Set.range F)) hJgen

    have hmaxeq : Module.finrank K (piece (Ideal.span (Set.range F)) (m + 1)) =
        Nat.macaulayPow m (Module.finrank K (piece (Ideal.span (Set.range F)) m)) := by
      apply le_antisymm (MvPolynomial.finrank_piece_succ_le_macaulayPow n m hm K _ hJh)
      obtain ⟨J₁, hJ₁, h1, h2⟩ :=
        MvPolynomial.exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow n m hm
          (Module.finrank K (piece (Ideal.span (Set.range F)) m)) (finrank_piece_le _ _) K
      rw [← h2]
      exact hmax J₁ hJ₁ h1

    refine descend (AlgebraicClosure K) F ?_ d c hc hcF
    intro d' c' hc' hrel
    have hFL : ∀ i, (map (algebraMap K (AlgebraicClosure K)) (F i)).IsHomogeneous m := fun i => (hF i).map _
    refine infinite_main (K := AlgebraicClosure K) n m hm g _ hFL ?_ d' c' hc' hrel
    have hJL : Ideal.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K))) (Ideal.span (Set.range F)) =
        Ideal.span (Set.range fun i => MvPolynomial.map (algebraMap K (AlgebraicClosure K)) (F i)) := by
      rw [Ideal.map_span, ← Set.range_comp]; rfl
    rw [← hJL, finrank_piece_map (AlgebraicClosure K) _ hJh, finrank_piece_map (AlgebraicClosure K) _ hJh]
    exact hmaxeq

end Assembly

end LinSyzCore
p2m_reactivate "P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le.LinSyzCore"

open MvPolynomial AlgebraicGeometry.HilbertFunctor in
theorem solution
    (n m g : ℕ) (K : Type) [Field K] (F : Fin g → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous m)
    (hmax : ∀ J' : Ideal (MvPolynomial (Fin (n + 1)) K),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J' = Ideal.span s) →
      Module.finrank K (piece J' m) = Module.finrank K (piece (Ideal.span (Set.range F)) m) →
      Module.finrank K (piece J' (m + 1)) ≤ Module.finrank K (piece (Ideal.span (Set.range F)) (m + 1)))
    (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K) (hc : ∀ i, (c i).IsHomogeneous d)
    (hcF : ∑ i, c i * F i = 0) :
    c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) K)
      {l : Fin g → MvPolynomial (Fin (n + 1)) K |
        (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i = 0} :=
  LinSyzCore.main n m g F hF hmax d c hc hcF

end S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le
end P2MW
export P2MW.S_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le (solution)
