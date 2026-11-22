-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_translation_continuous
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:13:33.071223+00:00
-- url     : https://prove2.me/submissions/980efe87-4558-4246-84d6-b5a2bf30267f

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Theorems.Thm_MasulloGRH_schwartzBruhat_averaging
import Theorems.Thm_MasulloGRH_elemSchwartz_frechet_nuclear_montel
import Theorems.Thm_MasulloGRH_schwartzBruhat_main_structure
import Theorems.Thm_MasulloGRH_exists_elemPresentation_of_isStructuralPair
import Theorems.Thm_MasulloGRH_isRapidDecay_elemSchwartz_toFun
import Theorems.Thm_MasulloGRH_elemSchwartz_continuous_of_seminorm_bound

open Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_schwartzBruhat_translation_continuous

open MasulloGRH Filter
open scoped ContDiff

universe u

section elem

variable {m n r s : ℕ} {d : Fin s → ℕ}

/-- Translation of functions on an elementary group. -/
def trE (e : ElemGroup m n r s d) (g : ElemGroup m n r s d → ℂ) : ElemGroup m n r s d → ℂ :=
  fun y => g (y - e)

lemma elemLift_trE (e : ElemGroup m n r s d) (g : ElemGroup m n r s d → ℂ) (t0 : Fin n → ℝ)
    (ht0 : ∀ j, ((t0 j : ℝ) : UnitAddCircle) = e.2.1 j) (a : Fin r → ℤ)
    (b : (i : Fin s) → ZMod (d i)) :
    elemLift (trE e g) a b =
      fun xt => elemLift g (a - e.2.2.1) (b - e.2.2.2) (xt - (e.1, t0)) := by
  funext xt
  simp only [elemLift, trE]
  congr 1
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext j
  show ((xt.2 j : ℝ) : UnitAddCircle) - e.2.1 j = ((xt.2 j - t0 j : ℝ) : UnitAddCircle)
  rw [← ht0 j, AddCircle.coe_sub]

lemma exists_small_lift (z : Fin n → UnitAddCircle) :
    ∃ t : Fin n → ℝ, (∀ j, ((t j : ℝ) : UnitAddCircle) = z j) ∧ ‖t‖ ≤ ‖z‖ := by
  have h : ∀ j, ∃ t : ℝ, ((t : ℝ) : UnitAddCircle) = z j ∧ |t| = ‖z j‖ := by
    intro j
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (z j)
    refine ⟨x - round x, ?_, ?_⟩
    · rw [AddCircle.coe_sub]
      have h0 : (((round x : ℤ) : ℝ) : UnitAddCircle) = 0 :=
        (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr ⟨round x, by simp⟩
      rw [h0, sub_zero]
      exact hx
    · rw [← hx]
      exact UnitAddCircle.norm_eq.symm
  choose t ht1 ht2 using h
  refine ⟨t, ht1, ?_⟩
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr fun j => ?_
  rw [Real.norm_eq_abs, ht2 j]
  exact norm_le_pi_norm z j

lemma pow_le_two_pow_mul {β β' X : ℝ} (hβ : 0 ≤ β) (hβ' : 0 ≤ β') (hX : 0 ≤ X)
    (h : β ≤ β' + X) (i : ℕ) : β ^ i ≤ 2 ^ i * (β' ^ i + X ^ i) := by
  calc β ^ i ≤ (β' + X) ^ i := pow_le_pow_left₀ hβ h i
    _ ≤ 2 ^ (i - 1) * (β' ^ i + X ^ i) := add_pow_le hβ' hX i
    _ ≤ 2 ^ i * (β' ^ i + X ^ i) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le i 1)

lemma weight_le {α α' A β β' X D : ℝ} (hα : 0 ≤ α) (hα' : 0 ≤ α') (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (hβ' : 0 ≤ β') (hX : 0 ≤ X) (hD : 0 ≤ D) (h1 : α ≤ α' + A) (h2 : β ≤ β' + X) (i j : ℕ) :
    α ^ j * β ^ i * D ≤ 2 ^ (i + j) * (α' ^ j * β' ^ i * D + X ^ i * (α' ^ j * β' ^ 0 * D) +
      A ^ j * (α' ^ 0 * β' ^ i * D) + A ^ j * X ^ i * (α' ^ 0 * β' ^ 0 * D)) := by
  have e1 := pow_le_two_pow_mul hα hα' hA h1 j
  have e2 := pow_le_two_pow_mul hβ hβ' hX h2 i
  calc α ^ j * β ^ i * D ≤ (2 ^ j * (α' ^ j + A ^ j)) * (2 ^ i * (β' ^ i + X ^ i)) * D :=
        mul_le_mul_of_nonneg_right (mul_le_mul e1 e2 (by positivity) (by positivity)) hD
    _ = _ := by ring

/-- The weighted derivative appearing in the seminorms. -/
noncomputable def Wt (g : ElemGroup m n r s d → ℂ) (k : ℕ) (a : Fin r → ℤ)
    (b : (i : Fin s) → ZMod (d i)) (y : (Fin m → ℝ) × (Fin n → ℝ)) (i j : ℕ) : ℝ :=
  ‖a‖ ^ j * ‖y.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift g a b) y‖

lemma trE_bound (e : ElemGroup m n r s d) (g : ElemGroup m n r s d → ℂ) (t0 : Fin n → ℝ)
    (ht0 : ∀ j, ((t0 j : ℝ) : UnitAddCircle) = e.2.1 j) (i j k : ℕ) (a : Fin r → ℤ)
    (b : (i : Fin s) → ZMod (d i)) (xt : (Fin m → ℝ) × (Fin n → ℝ)) :
    ‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift (trE e g) a b) xt‖ ≤
      2 ^ (i + j) * (Wt g k (a - e.2.2.1) (b - e.2.2.2) (xt - (e.1, t0)) i j +
        ‖e.1‖ ^ i * Wt g k (a - e.2.2.1) (b - e.2.2.2) (xt - (e.1, t0)) 0 j +
        ‖e.2.2.1‖ ^ j * Wt g k (a - e.2.2.1) (b - e.2.2.2) (xt - (e.1, t0)) i 0 +
        ‖e.2.2.1‖ ^ j * ‖e.1‖ ^ i * Wt g k (a - e.2.2.1) (b - e.2.2.2) (xt - (e.1, t0)) 0 0) := by
  rw [elemLift_trE e g t0 ht0 a b, iteratedFDeriv_comp_sub]
  unfold Wt
  apply weight_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  · calc ‖a‖ = ‖(a - e.2.2.1) + e.2.2.1‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  · calc ‖xt.1‖ = ‖(xt - (e.1, t0)).1 + e.1‖ := by rw [Prod.fst_sub, sub_add_cancel]
      _ ≤ _ := norm_add_le _ _

lemma isRapidDecay_trE (e : ElemGroup m n r s d) (g : ElemGroup m n r s d → ℂ)
    (hg : IsRapidDecay g) : IsRapidDecay (trE e g) := by
  obtain ⟨t0, ht0, -⟩ := exists_small_lift e.2.1
  refine ⟨fun a b => ?_, fun i j k => ?_⟩
  · rw [elemLift_trE e g t0 ht0 a b]
    exact (hg.1 _ _).comp (contDiff_id.sub contDiff_const)
  · obtain ⟨C1, hC1⟩ := hg.2 i j k
    obtain ⟨C2, hC2⟩ := hg.2 0 j k
    obtain ⟨C3, hC3⟩ := hg.2 i 0 k
    obtain ⟨C4, hC4⟩ := hg.2 0 0 k
    refine ⟨2 ^ (i + j) * (C1 + ‖e.1‖ ^ i * C2 + ‖e.2.2.1‖ ^ j * C3 +
      ‖e.2.2.1‖ ^ j * ‖e.1‖ ^ i * C4), fun a b xt => ?_⟩
    refine (trE_bound e g t0 ht0 i j k a b xt).trans ?_
    have h1 := hC1 (a - e.2.2.1) (b - e.2.2.2) (xt - (e.1, t0))
    have h2 := hC2 (a - e.2.2.1) (b - e.2.2.2) (xt - (e.1, t0))
    have h3 := hC3 (a - e.2.2.1) (b - e.2.2.2) (xt - (e.1, t0))
    have h4 := hC4 (a - e.2.2.1) (b - e.2.2.2) (xt - (e.1, t0))
    unfold Wt
    gcongr

/-- Translation as an additive endomorphism of the elementary Schwartz space. -/
noncomputable def τE (e : ElemGroup m n r s d) : ElemSchwartz m n r s d →+ ElemSchwartz m n r s d where
  toFun g := ⟨trE e g.toFun, Submodule.subset_span
    (isRapidDecay_trE e g.toFun (isRapidDecay_elemSchwartz_toFun g))⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

lemma τE_toFun (e : ElemGroup m n r s d) (g : ElemSchwartz m n r s d) :
    (τE e g).toFun = trE e g.toFun := rfl

lemma τE_continuous (e : ElemGroup m n r s d) : Continuous (τE e) := by
  obtain ⟨t0, ht0, -⟩ := exists_small_lift e.2.1
  refine elemSchwartz_continuous_of_seminorm_bound (τE e) fun p => ⟨{(p.1, p.2.1, p.2.2),
    (0, p.2.1, p.2.2), (p.1, 0, p.2.2), (0, 0, p.2.2)}, 2 ^ (p.1 + p.2.1) *
    (1 + ‖e.1‖ ^ p.1 + ‖e.2.2.1‖ ^ p.2.1 + ‖e.2.2.1‖ ^ p.2.1 * ‖e.1‖ ^ p.1),
    fun g M hM a b xt => ?_⟩
  rw [τE_toFun]
  refine (trE_bound e g.toFun t0 ht0 p.1 p.2.1 p.2.2 a b xt).trans ?_
  have h1 := hM (p.1, p.2.1, p.2.2) (by simp) (a - e.2.2.1) (b - e.2.2.2) (xt - (e.1, t0))
  have h2 := hM (0, p.2.1, p.2.2) (by simp) (a - e.2.2.1) (b - e.2.2.2) (xt - (e.1, t0))
  have h3 := hM (p.1, 0, p.2.2) (by simp) (a - e.2.2.1) (b - e.2.2.2) (xt - (e.1, t0))
  have h4 := hM (0, 0, p.2.2) (by simp) (a - e.2.2.1) (b - e.2.2.2) (xt - (e.1, t0))
  dsimp only at h1 h2 h3 h4
  unfold Wt
  calc _ ≤ 2 ^ (p.1 + p.2.1) * (M + ‖e.1‖ ^ p.1 * M + ‖e.2.2.1‖ ^ p.2.1 * M +
        ‖e.2.2.1‖ ^ p.2.1 * ‖e.1‖ ^ p.1 * M) := by gcongr
    _ = _ := by ring

/-- Neighbourhoods in the elementary Schwartz space. -/
lemma tendsto_ES {X : Type*} {l : Filter X} {F : X → ElemSchwartz m n r s d}
    {g₀ : ElemSchwartz m n r s d} :
    Tendsto F l (𝓝 g₀) ↔ ∀ p : ℕ × ℕ × ℕ, ∀ ε > 0, ∀ᶠ x in l, ∀ a b xt,
      ‖a‖ ^ p.2.1 * ‖xt.1‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2.2 (elemLift (F x).toFun a b) xt -
        iteratedFDeriv ℝ p.2.2 (elemLift g₀.toFun a b) xt‖ < ε := by
  let Ψ := fun (g : ElemSchwartz m n r s d) (p : ℕ × ℕ × ℕ) =>
      UniformFun.ofFun
        (fun q : (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)) × ((Fin m → ℝ) × (Fin n → ℝ)) =>
          (‖q.1‖ ^ p.2.1 * ‖q.2.2.1‖ ^ p.1) •
            iteratedFDeriv ℝ p.2.2 (elemLift g.toFun q.1 q.2.1) q.2.2)
  have hI : IsInducing Ψ := ⟨rfl⟩
  rw [hI.tendsto_nhds_iff, tendsto_pi_nhds]
  refine forall_congr' fun p => ?_
  rw [UniformFun.tendsto_iff_tendstoUniformly, Metric.tendstoUniformly_iff]
  refine forall₂_congr fun ε _ => ?_
  refine eventually_congr (Eventually.of_forall fun x => ?_)
  have key : ∀ a b xt, dist (UniformFun.toFun (Ψ g₀ p) (a, b, xt))
      ((UniformFun.toFun ∘ fun i => (Ψ ∘ F) i p) x (a, b, xt)) < ε ↔
      ‖a‖ ^ p.2.1 * ‖xt.1‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2.2 (elemLift (F x).toFun a b) xt -
        iteratedFDeriv ℝ p.2.2 (elemLift g₀.toFun a b) xt‖ < ε := by
    intro a b xt
    have hw : 0 ≤ ‖a‖ ^ p.2.1 * ‖xt.1‖ ^ p.1 := by positivity
    show dist ((‖a‖ ^ p.2.1 * ‖xt.1‖ ^ p.1) • iteratedFDeriv ℝ p.2.2 (elemLift g₀.toFun a b) xt)
        ((‖a‖ ^ p.2.1 * ‖xt.1‖ ^ p.1) • iteratedFDeriv ℝ p.2.2 (elemLift (F x).toFun a b) xt) < ε ↔ _
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg hw, norm_sub_rev]
  exact ⟨fun h a b xt => (key a b xt).mp (h (a, b, xt)),
    fun h q => (key q.1 q.2.1 q.2.2).mpr (h q.1 q.2.1 q.2.2)⟩

/-- The analytic estimate behind the continuity of translation at the origin. -/
lemma key_est (F G : (Fin m → ℝ) × (Fin n → ℝ) → ℂ) (hG : ContDiff ℝ ∞ G) (k i : ℕ) (w : ℝ)
    (hw : 0 ≤ w) (v xt : (Fin m → ℝ) × (Fin n → ℝ)) (hv : ‖v‖ ≤ 1) (δ B : ℝ)
    (hΔ : ∀ y : (Fin m → ℝ) × (Fin n → ℝ),
      w * ‖y.1‖ ^ i * ‖iteratedFDeriv ℝ k F y - iteratedFDeriv ℝ k G y‖ < δ)
    (hΔ0 : ∀ y : (Fin m → ℝ) × (Fin n → ℝ),
      w * ‖y.1‖ ^ 0 * ‖iteratedFDeriv ℝ k F y - iteratedFDeriv ℝ k G y‖ < δ)
    (hB : ∀ z : (Fin m → ℝ) × (Fin n → ℝ), w * ‖z.1‖ ^ i * ‖iteratedFDeriv ℝ (k + 1) G z‖ ≤ B)
    (hB0 : ∀ z : (Fin m → ℝ) × (Fin n → ℝ),
      w * ‖z.1‖ ^ 0 * ‖iteratedFDeriv ℝ (k + 1) G z‖ ≤ B) :
    w * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k F (xt - v) - iteratedFDeriv ℝ k G xt‖ ≤
      2 ^ i * (2 * δ) + 2 ^ i * (2 * B) * ‖v‖ := by
  have hwt : ∀ z : (Fin m → ℝ) × (Fin n → ℝ), ‖xt - z‖ ≤ 1 →
      w * ‖xt.1‖ ^ i ≤ 2 ^ i * (w * ‖z.1‖ ^ i + w * ‖z.1‖ ^ 0) := by
    intro z hz
    have h1 : ‖xt.1‖ ≤ ‖z.1‖ + 1 := by
      calc ‖xt.1‖ = ‖z.1 + (xt - z).1‖ := by rw [Prod.fst_sub, add_sub_cancel]
        _ ≤ ‖z.1‖ + ‖(xt - z).1‖ := norm_add_le _ _
        _ ≤ ‖z.1‖ + 1 := by gcongr; exact (norm_fst_le _).trans hz
    have h2 := pow_le_two_pow_mul (norm_nonneg _) (norm_nonneg _) zero_le_one h1 i
    rw [one_pow] at h2
    calc w * ‖xt.1‖ ^ i ≤ w * (2 ^ i * (‖z.1‖ ^ i + 1)) := mul_le_mul_of_nonneg_left h2 hw
      _ = _ := by ring
  have hc : 0 ≤ w * ‖xt.1‖ ^ i := by positivity
  have t1 : w * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k F (xt - v) - iteratedFDeriv ℝ k G (xt - v)‖ ≤
      2 ^ i * (2 * δ) := by
    have h := hwt (xt - v) (by rw [sub_sub_cancel]; exact hv)
    have a1 := hΔ (xt - v)
    have a2 := hΔ0 (xt - v)
    calc _ ≤ 2 ^ i * (w * ‖(xt - v).1‖ ^ i + w * ‖(xt - v).1‖ ^ 0) *
          ‖iteratedFDeriv ℝ k F (xt - v) - iteratedFDeriv ℝ k G (xt - v)‖ :=
          mul_le_mul_of_nonneg_right h (norm_nonneg _)
      _ = 2 ^ i * (w * ‖(xt - v).1‖ ^ i *
            ‖iteratedFDeriv ℝ k F (xt - v) - iteratedFDeriv ℝ k G (xt - v)‖ +
          w * ‖(xt - v).1‖ ^ 0 *
            ‖iteratedFDeriv ℝ k F (xt - v) - iteratedFDeriv ℝ k G (xt - v)‖) := by ring
      _ ≤ 2 ^ i * (δ + δ) := by gcongr
      _ = _ := by ring
  have hdiff : ∀ z, DifferentiableAt ℝ (iteratedFDeriv ℝ k G) z := fun z =>
    (hG.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top k)) z
  have t2 : ‖(w * ‖xt.1‖ ^ i) • iteratedFDeriv ℝ k G (xt - v) -
      (w * ‖xt.1‖ ^ i) • iteratedFDeriv ℝ k G xt‖ ≤ 2 ^ i * (2 * B) * ‖v‖ := by
    have hbound : ∀ z ∈ Metric.closedBall xt ‖v‖,
        ‖fderiv ℝ (fun z => (w * ‖xt.1‖ ^ i) • iteratedFDeriv ℝ k G z) z‖ ≤ 2 ^ i * (2 * B) := by
      intro z hz
      rw [fderiv_fun_const_smul (hdiff z)]
      refine (ContinuousLinearMap.opNorm_smul_le (w * ‖xt.1‖ ^ i)
        (fderiv ℝ (iteratedFDeriv ℝ k G) z)).trans ?_
      rw [norm_fderiv_iteratedFDeriv, Real.norm_of_nonneg hc]
      have hz' : ‖xt - z‖ ≤ 1 := by
        rw [← dist_eq_norm, dist_comm]
        exact (Metric.mem_closedBall.mp hz).trans hv
      have h := hwt z hz'
      have b1 := hB z
      have b2 := hB0 z
      calc _ ≤ 2 ^ i * (w * ‖z.1‖ ^ i + w * ‖z.1‖ ^ 0) * ‖iteratedFDeriv ℝ (k + 1) G z‖ :=
            mul_le_mul_of_nonneg_right h (norm_nonneg _)
        _ = 2 ^ i * (w * ‖z.1‖ ^ i * ‖iteratedFDeriv ℝ (k + 1) G z‖ +
            w * ‖z.1‖ ^ 0 * ‖iteratedFDeriv ℝ (k + 1) G z‖) := by ring
        _ ≤ 2 ^ i * (B + B) := by gcongr
        _ = _ := by ring
    have hmem1 : xt ∈ Metric.closedBall xt ‖v‖ := Metric.mem_closedBall_self (norm_nonneg v)
    have hmem2 : xt - v ∈ Metric.closedBall xt ‖v‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]
    have h := (convex_closedBall xt ‖v‖).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hdiff z).const_smul (w * ‖xt.1‖ ^ i)) hbound hmem1 hmem2
    rwa [sub_sub_cancel_left, norm_neg] at h
  calc w * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k F (xt - v) - iteratedFDeriv ℝ k G xt‖ ≤
      w * ‖xt.1‖ ^ i * (‖iteratedFDeriv ℝ k F (xt - v) - iteratedFDeriv ℝ k G (xt - v)‖ +
        ‖iteratedFDeriv ℝ k G (xt - v) - iteratedFDeriv ℝ k G xt‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub _ _ _) hc
    _ = w * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k F (xt - v) - iteratedFDeriv ℝ k G (xt - v)‖ +
        ‖(w * ‖xt.1‖ ^ i) • iteratedFDeriv ℝ k G (xt - v) -
          (w * ‖xt.1‖ ^ i) • iteratedFDeriv ℝ k G xt‖ := by
        rw [mul_add, ← smul_sub, norm_smul, Real.norm_of_nonneg hc]
    _ ≤ _ := add_le_add t1 t2

lemma τE_zero_cont (g₀ : ElemSchwartz m n r s d) :
    Tendsto (fun x : ElemGroup m n r s d × ElemSchwartz m n r s d => τE x.1 x.2)
      (𝓝 (0, g₀)) (𝓝 g₀) := by
  rw [tendsto_ES]
  rintro ⟨i, j, k⟩ ε hε
  have hg₀ := isRapidDecay_elemSchwartz_toFun g₀
  obtain ⟨C1, hC1⟩ := hg₀.2 i j (k + 1)
  obtain ⟨C2, hC2⟩ := hg₀.2 0 j (k + 1)
  set B := max (max C1 C2) 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  set δ := ε / (4 * 2 ^ i) with hδdef
  have hδ : 0 < δ := by positivity
  set η := min 1 (ε / (4 * 2 ^ i * (B + 1))) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  have ev1 := (tendsto_ES.mp (tendsto_id (x := 𝓝 g₀))) (i, j, k) δ hδ
  have ev2 := (tendsto_ES.mp (tendsto_id (x := 𝓝 g₀))) (0, j, k) δ hδ
  have c0 : Tendsto (fun h : ElemGroup m n r s d => h.2.2) (𝓝 0) (𝓝 0) := by
    simpa using ((continuous_snd.comp continuous_snd).tendsto (0 : ElemGroup m n r s d))
  have c1 : Tendsto (fun h : ElemGroup m n r s d => ‖h.1‖) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_fst.norm.tendsto (0 : ElemGroup m n r s d))
  have c2 : Tendsto (fun h : ElemGroup m n r s d => ‖h.2.1‖) (𝓝 0) (𝓝 0) := by
    simpa using ((continuous_fst.comp continuous_snd).norm.tendsto (0 : ElemGroup m n r s d))
  have evh : ∀ᶠ h : ElemGroup m n r s d in 𝓝 0, h.2.2 = 0 ∧ ‖h.1‖ < η ∧ ‖h.2.1‖ < η :=
    (show ∀ᶠ h : ElemGroup m n r s d in 𝓝 0, h.2.2 = 0 from
      c0 ((isOpen_discrete {0}).mem_nhds rfl)).and
      ((c1.eventually (gt_mem_nhds hη)).and (c2.eventually (gt_mem_nhds hη)))
  rw [nhds_prod_eq]
  filter_upwards [evh.prod_mk (ev1.and ev2)] with x hx
  obtain ⟨⟨h0, hη1, hη2⟩, hx1, hx2⟩ := hx
  intro a b xt
  obtain ⟨t, ht, htn⟩ := exists_small_lift x.1.2.1
  have hv : ‖((x.1.1, t) : (Fin m → ℝ) × (Fin n → ℝ))‖ < η := by
    rw [Prod.norm_def]
    exact max_lt hη1 (htn.trans_lt hη2)
  have ha : a - x.1.2.2.1 = a := by rw [show x.1.2.2.1 = 0 from congrArg Prod.fst h0, sub_zero]
  have hb : b - x.1.2.2.2 = b := by rw [show x.1.2.2.2 = 0 from congrArg Prod.snd h0, sub_zero]
  rw [τE_toFun, elemLift_trE x.1 x.2.toFun t ht a b, ha, hb, iteratedFDeriv_comp_sub]
  have hG : ContDiff ℝ ∞ (elemLift g₀.toFun a b) := hg₀.1 a b
  have hest := key_est (elemLift x.2.toFun a b) (elemLift g₀.toFun a b) hG k i (‖a‖ ^ j)
    (by positivity) (x.1.1, t) xt (hv.le.trans (min_le_left _ _)) δ B
    (fun y => hx1 a b y) (fun y => hx2 a b y)
    (fun z => (hC1 a b z).trans ((le_max_left _ _).trans (le_max_left _ _)))
    (fun z => (hC2 a b z).trans ((le_max_right _ _).trans (le_max_left _ _)))
  have e1 : (2 : ℝ) ^ i * (2 * δ) = ε / 2 := by
    rw [hδdef]
    field_simp
    ring
  have e2 : (2 : ℝ) ^ i * (2 * B) * ‖((x.1.1, t) : (Fin m → ℝ) × (Fin n → ℝ))‖ < ε / 2 := by
    calc (2 : ℝ) ^ i * (2 * B) * ‖((x.1.1, t) : (Fin m → ℝ) × (Fin n → ℝ))‖ ≤
        2 ^ i * (2 * (B + 1)) * ‖((x.1.1, t) : (Fin m → ℝ) × (Fin n → ℝ))‖ := by
          gcongr
          linarith
      _ < 2 ^ i * (2 * (B + 1)) * η := by
          apply mul_lt_mul_of_pos_left hv
          positivity
      _ ≤ 2 ^ i * (2 * (B + 1)) * (ε / (4 * 2 ^ i * (B + 1))) := by
          gcongr
          exact min_le_right _ _
      _ = ε / 2 := by
          field_simp
          ring
  have : ‖a‖ ^ j * ‖xt.1‖ ^ i = ‖a‖ ^ j * ‖xt.1‖ ^ i := rfl
  calc _ ≤ _ := hest
    _ < ε / 2 + ε / 2 := by rw [e1]; linarith
    _ = ε := by ring

lemma τE_add (e h : ElemGroup m n r s d) (g : ElemSchwartz m n r s d) :
    τE e (τE h g) = τE (e + h) g := by
  apply Subtype.ext
  funext y
  show g.toFun (y - e - h) = g.toFun (y - (e + h))
  rw [sub_sub]

theorem elem_translation :
    ∃ τ : ElemGroup m n r s d → ElemSchwartz m n r s d → ElemSchwartz m n r s d,
      (∀ e g y, (τ e g).toFun y = g.toFun (y - e)) ∧
      Continuous (fun p : ElemGroup m n r s d × ElemSchwartz m n r s d => τ p.1 p.2) := by
  refine ⟨fun e g => τE e g, fun e g y => rfl, ?_⟩
  rw [continuous_iff_continuousAt]
  rintro ⟨e₀, g₀⟩
  have hφ : Tendsto (fun x : ElemGroup m n r s d × ElemSchwartz m n r s d => (x.1 - e₀, x.2))
      (𝓝 (e₀, g₀)) (𝓝 (0, g₀)) := by
    have hc : Continuous (fun x : ElemGroup m n r s d × ElemSchwartz m n r s d =>
        (x.1 - e₀, x.2)) := (continuous_fst.sub continuous_const).prodMk continuous_snd
    simpa using hc.tendsto (e₀, g₀)
  have h1 := ((τE_continuous e₀).tendsto g₀).comp ((τE_zero_cont g₀).comp hφ)
  refine h1.congr fun x => ?_
  show τE e₀ (τE (x.1 - e₀) x.2) = τE x.1 x.2
  rw [τE_add, add_sub_cancel]

end elem


section group

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

lemma topology_eq : instTopologicalSpaceSchwartzBruhat G =
    sInf {t | IsLocallyConvexTopology (SchwartzBruhat G) t ∧
    ∀ (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
      (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
      (hπ : IsElemPresentation Γ k π),
      @Continuous (ElemSchwartz m n r s d) (SchwartzBruhat G) _ t
        (SchwartzBruhat.ofElem Γ k π hs hπ)} := rfl

lemma ofElem_continuous {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : Continuous (SchwartzBruhat.ofElem Γ k π hs hπ) := by
  rw [continuous_iff_le_induced, topology_eq, ← continuous_iff_le_induced, continuous_sInf_rng]
  intro t ht
  exact ht.2 Γ k m n r s d π hs hπ

/-- The inclusion of a stage as a linear map. -/
noncomputable def ofElemL {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : ElemSchwartz m n r s d →ₗ[ℂ] SchwartzBruhat G where
  toFun := SchwartzBruhat.ofElem Γ k π hs hπ
  map_add' g g' := by
    apply Subtype.ext
    show extendPullback Γ π (g + g').toFun =
      extendPullback Γ π g.toFun + extendPullback Γ π g'.toFun
    funext x
    simp only [extendPullback, Pi.add_apply]
    split_ifs
    · rfl
    · simp
  map_smul' c g := by
    apply Subtype.ext
    show extendPullback Γ π (c • g).toFun = c • extendPullback Γ π g.toFun
    funext x
    simp only [extendPullback, Pi.smul_apply]
    split_ifs
    · rfl
    · simp

/-- Universal property of the inductive limit topology for seminorms. -/
lemma seminorm_continuous_of_ofElem (q : Seminorm ℂ (SchwartzBruhat G))
    (hq : ∀ (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
      (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
      (hπ : IsElemPresentation Γ k π),
      Continuous (fun g => q (SchwartzBruhat.ofElem Γ k π hs hπ g))) :
    Continuous q := by
  let p : SeminormFamily ℂ (SchwartzBruhat G) PUnit.{u+1} := fun _ => q
  let t : TopologicalSpace (SchwartzBruhat G) := p.moduleFilterBasis.topology
  have hp : @WithSeminorms ℂ (SchwartzBruhat G) PUnit.{u+1} _ _ _ p t := ⟨rfl⟩
  have hle : instTopologicalSpaceSchwartzBruhat G ≤ t := by
    rw [topology_eq]
    refine sInf_le ⟨⟨PUnit.{u+1}, inferInstance, p, hp⟩, ?_⟩
    intro Γ k m n r s d π hs hπ
    obtain ⟨ι, _, P, hP⟩ := (elemSchwartz_frechet_nuclear_montel m n r s d hπ.1).1.1
    have : IsTopologicalAddGroup (ElemSchwartz m n r s d) := hP.topologicalAddGroup
    letI : TopologicalSpace (SchwartzBruhat G) := t
    exact hp.continuous_of_continuous_comp (ofElemL Γ k π hs hπ)
      (fun _ => hq Γ k m n r s d π hs hπ)
  have h1 : @Continuous _ _ t _ q := @WithSeminorms.continuous_seminorm ℂ (SchwartzBruhat G)
    PUnit.{u+1} _ _ _ t p hp PUnit.unit
  exact @Continuous.comp _ _ _ (instTopologicalSpaceSchwartzBruhat G) t _ _ _ h1
    (continuous_id_of_le hle)

/-- Left translation of functions. -/
def trF (g : G) (f : G → ℂ) : G → ℂ := fun x => f (g⁻¹ * x)

lemma trF_extendPullback {m n r s : ℕ} {d : Fin s → ℕ} (Γ : Subgroup G)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (u : ElemGroup m n r s d → ℂ) (h : G)
    (hh : h ∈ Γ) :
    trF h (extendPullback Γ π u) =
      extendPullback Γ π (fun y => u (y - Multiplicative.toAdd (π ⟨h, hh⟩))) := by
  funext x
  by_cases hx : x ∈ Γ
  · have hmem : h⁻¹ * x ∈ Γ := Γ.mul_mem (Γ.inv_mem hh) hx
    have hprod : (⟨h⁻¹ * x, hmem⟩ : Γ) = (⟨h, hh⟩ : Γ)⁻¹ * ⟨x, hx⟩ := rfl
    simp only [trF, extendPullback, dif_pos hx, dif_pos hmem, hprod, map_mul, map_inv, toAdd_mul,
      toAdd_inv]
    congr 1
    abel
  · have hmem : h⁻¹ * x ∉ Γ := fun hm => hx (by simpa using Γ.mul_mem hh hm)
    simp only [trF, extendPullback, dif_neg hx, dif_neg hmem]

variable [T2Space G] [LocallyCompactSpace G]

/-- A stage can be enlarged so that its open subgroup contains a given element. -/
lemma exists_enlarge {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) (g₀ : G) :
    ∃ (Γ' k' : Subgroup G) (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
      (π' : ↥Γ' →* Multiplicative (ElemGroup m' n' r' s' d')) (hs' : IsStructuralPair Γ' k')
      (hπ' : IsElemPresentation Γ' k' π')
      (T : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m' n' r' s' d'),
      g₀ ∈ Γ' ∧ Continuous T ∧
        ∀ g, SchwartzBruhat.ofElem Γ k π hs hπ g = SchwartzBruhat.ofElem Γ' k' π' hs' hπ' (T g) := by
  have hs0 := hs
  obtain ⟨hΓo, ⟨U, hUc, -, ⟨V, hV, hVU⟩, hUcl⟩, hk, hkΓ⟩ := hs0
  let Γ' := Subgroup.closure (insert g₀ U)
  have hle : Γ ≤ Γ' := by
    rw [← hUcl]
    exact Subgroup.closure_mono (Set.subset_insert _ _)
  have hs' : IsStructuralPair Γ' k := by
    refine ⟨Subgroup.isOpen_mono hle hΓo, ⟨insert g₀ U, hUc.insert g₀, Subgroup.subset_closure,
      ⟨V ∩ Γ, Filter.inter_mem hV (hΓo.mem_nhds Γ.one_mem), ?_⟩, rfl⟩, hk, hkΓ.trans hle⟩
    intro x hx
    exact Set.mem_insert_of_mem _ (hVU ⟨hx.1.1, hx.1.2⟩)
  obtain ⟨m', n', r', s', d', π', hπ'⟩ := exists_elemPresentation_of_isStructuralPair G Γ' k hs'
  obtain ⟨A, -, h2, -, h4⟩ := schwartzBruhat_averaging G
  obtain ⟨T, hT, hTeq⟩ := h4 Γ k m n r s d π hs hπ Γ' k m' n' r' s' d' π' hs' hπ'
  refine ⟨Γ', k, m', n', r', s', d', π', hs', hπ', T,
    Subgroup.subset_closure (Set.mem_insert _ _), hT, fun g => ?_⟩
  rw [← hTeq g]
  exact (h2 Γ k m n r s d π hs hπ Γ' k hs' hle le_rfl g).symm

lemma trF_mem (g : G) (f : G → ℂ) (hf : f ∈ schwartzBruhatSubmodule G) :
    trF g f ∈ schwartzBruhatSubmodule G := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨Γ, k, m, n, r, s, d, π, u, hs, hπ, rfl⟩ := hf
    obtain ⟨Γ', k', m', n', r', s', d', π', hs', hπ', T, hg, -, hT⟩ :=
      exists_enlarge Γ k π hs hπ g
    obtain ⟨τ, hτ, -⟩ := elem_translation (m := m') (n := n') (r := r') (s := s') (d := d')
    have h1 : extendPullback Γ π u.toFun = extendPullback Γ' π' (T u).toFun :=
      congrArg Subtype.val (hT u)
    rw [h1, trF_extendPullback Γ' π' _ g hg]
    refine Submodule.subset_span ⟨Γ', k', m', n', r', s', d', π',
      τ (Multiplicative.toAdd (π' ⟨g, hg⟩)) (T u), hs', hπ', ?_⟩
    congr 1
    funext y
    exact (hτ _ _ y).symm
  | zero => exact Submodule.zero_mem _
  | add f₁ f₂ _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | smul c f _ h => exact Submodule.smul_mem _ c h

/-- Left translation on `S(G)`. -/
noncomputable def ρ (g : G) : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat G where
  toFun f := ⟨trF g f.1, trF_mem g f.1 f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma stage_continuous {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) :
    Continuous (fun p : G × ElemSchwartz m n r s d =>
      ρ p.1 (SchwartzBruhat.ofElem Γ k π hs hπ p.2)) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨g₀, s₀⟩
  obtain ⟨Γ', k', m', n', r', s', d', π', hs', hπ', T, hg, hTc, hT⟩ :=
    exists_enlarge Γ k π hs hπ g₀
  obtain ⟨τ, hτ, hτc⟩ := elem_translation (m := m') (n := n') (r := r') (s := s') (d := d')
  have hOpen : IsOpenEmbedding (Prod.map (Subtype.val : Γ' → G)
      (id : ElemSchwartz m n r s d → ElemSchwartz m n r s d)) :=
    hs'.1.isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id
  apply (hOpen.continuousAt_iff (x := (⟨g₀, hg⟩, s₀))).mp
  have hcont : Continuous (fun p : Γ' × ElemSchwartz m n r s d =>
      SchwartzBruhat.ofElem Γ' k' π' hs' hπ' (τ (Multiplicative.toAdd (π' p.1)) (T p.2))) :=
    (ofElem_continuous Γ' k' π' hs' hπ').comp (hτc.comp
      ((continuous_toAdd.comp (hπ'.2.1.comp continuous_fst)).prodMk (hTc.comp continuous_snd)))
  refine (hcont.congr fun p => ?_).continuousAt
  apply Subtype.ext
  show extendPullback Γ' π' (τ _ (T p.2)).toFun = trF p.1.1 (extendPullback Γ π p.2.toFun)
  have h1 : extendPullback Γ π p.2.toFun = extendPullback Γ' π' (T p.2).toFun :=
    congrArg Subtype.val (hT p.2)
  rw [h1]
  rw [trF_extendPullback Γ' π' _ p.1.1 p.1.2]
  congr 1
  funext y
  exact hτ _ _ y

section top

variable [IsTopologicalAddGroup (SchwartzBruhat G)] [ContinuousSMul ℂ (SchwartzBruhat G)]

lemma orbit_continuous (f : SchwartzBruhat G) : Continuous (fun g => ρ g f) := by
  obtain ⟨f, hf⟩ := f
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨Γ, k, m, n, r, s, d, π, u, hs, hπ, rfl⟩ := hf
    exact (stage_continuous Γ k π hs hπ).comp (continuous_id.prodMk continuous_const)
  | zero =>
    have : (fun g => ρ g (⟨0, Submodule.zero_mem _⟩ : SchwartzBruhat G)) = fun _ => 0 := by
      funext g
      rfl
    rw [this]
    exact continuous_const
  | add f₁ f₂ h₁ h₂ ih₁ ih₂ =>
    have : (fun g => ρ g (⟨f₁ + f₂, Submodule.add_mem _ h₁ h₂⟩ : SchwartzBruhat G)) =
        fun g => ρ g ⟨f₁, h₁⟩ + ρ g ⟨f₂, h₂⟩ := by
      funext g
      rfl
    rw [this]
    exact ih₁.add ih₂
  | smul c f h ih =>
    have : (fun g => ρ g (⟨c • f, Submodule.smul_mem _ c h⟩ : SchwartzBruhat G)) =
        fun g => c • ρ g ⟨f, h⟩ := by
      funext g
      rfl
    rw [this]
    exact ih.const_smul c

lemma supSeminorm (q : Seminorm ℂ (SchwartzBruhat G)) (hq : Continuous q) (K : Set G)
    (hK : IsCompact K) :
    ∃ Q : Seminorm ℂ (SchwartzBruhat G), Continuous Q ∧ ∀ g ∈ K, ∀ f, q (ρ g f) ≤ Q f := by
  have hbdd : BddAbove (Set.range (fun g : K => q.comp (ρ g.1))) := by
    rw [Seminorm.bddAbove_range_iff]
    intro f
    obtain ⟨C, hC⟩ := (hK.image (hq.comp (orbit_continuous f))).bddAbove
    exact ⟨C, by rintro _ ⟨g, rfl⟩; exact hC ⟨g.1, g.2, rfl⟩⟩
  refine ⟨⨆ g : K, q.comp (ρ g.1), ?_, fun g hg f => ?_⟩
  · apply seminorm_continuous_of_ofElem
    intro Γ k m n r s d π hs hπ
    have : (fun u => (⨆ g : K, q.comp (ρ g.1)) (SchwartzBruhat.ofElem Γ k π hs hπ u)) =
        fun u => sSup ((fun g => q (ρ g (SchwartzBruhat.ofElem Γ k π hs hπ u))) '' K) := by
      funext u
      rw [Seminorm.coe_iSup_eq hbdd, iSup_apply, sSup_image']
      rfl
    rw [this]
    exact hK.continuous_sSup
      (f := fun u g => q (ρ g (SchwartzBruhat.ofElem Γ k π hs hπ u)))
      (hq.comp ((stage_continuous Γ k π hs hπ).comp continuous_swap))
  · rw [Seminorm.coe_iSup_eq hbdd, iSup_apply]
    exact le_ciSup (f := fun g : K => (q.comp (ρ g.1)) f)
      (Seminorm.bddAbove_range_iff.mp hbdd f) ⟨g, hg⟩

lemma equicont {ι : Type u} {p : SeminormFamily ℂ (SchwartzBruhat G) ι} (hp : WithSeminorms p)
    (K : Set G) (hK : IsCompact K) (U : Set (SchwartzBruhat G)) (hU : U ∈ 𝓝 0) :
    ∃ V ∈ 𝓝 (0 : SchwartzBruhat G), ∀ g ∈ K, ∀ f ∈ V, ρ g f ∈ U := by
  obtain ⟨⟨S, r⟩, hr, hsub⟩ := hp.hasBasis_zero_ball.mem_iff.mp hU
  have hqc : Continuous ((S.sup p : Seminorm ℂ (SchwartzBruhat G)) : SchwartzBruhat G → ℝ) :=
    Seminorm.continuous_finsetSup fun i _ => hp.continuous_seminorm i
  obtain ⟨Q, hQc, hQ⟩ := supSeminorm (S.sup p) hqc K hK
  refine ⟨Q.ball 0 r, Seminorm.ball_mem_nhds hQc hr, fun g hg f hf => hsub ?_⟩
  rw [Seminorm.mem_ball_zero] at hf ⊢
  exact lt_of_le_of_lt (hQ g hg f) hf

lemma joint {ι : Type u} {p : SeminormFamily ℂ (SchwartzBruhat G) ι} (hp : WithSeminorms p) :
    Continuous (fun x : G × SchwartzBruhat G => ρ x.1 x.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨g₀, f₀⟩
  have h1 : Tendsto (fun x : G × SchwartzBruhat G => ρ x.1 (x.2 - f₀)) (𝓝 (g₀, f₀)) (𝓝 0) := by
    intro U hU
    obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds g₀
    obtain ⟨V, hV, hVU⟩ := equicont hp K hK U hU
    have hV' : (fun f => f - f₀) ⁻¹' V ∈ 𝓝 f₀ :=
      (continuous_sub_right f₀).continuousAt.preimage_mem_nhds (by simpa using hV)
    rw [Filter.mem_map]
    filter_upwards [prod_mem_nhds hKn hV'] with x hx
    exact hVU x.1 hx.1 _ hx.2
  have h2 : ContinuousAt (fun x : G × SchwartzBruhat G => ρ x.1 f₀) (g₀, f₀) :=
    ((orbit_continuous f₀).comp continuous_fst).continuousAt
  have h3 := h1.add h2
  rw [zero_add] at h3
  refine h3.congr fun x => ?_
  simp only [map_sub, sub_add_cancel]

end top

end group

end Sol_MasulloGRH_schwartzBruhat_translation_continuous

open MasulloGRH Sol_MasulloGRH_schwartzBruhat_translation_continuous in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] :
    ∃ ρ : G → SchwartzBruhat G → SchwartzBruhat G,
      (∀ (g : G) (f : SchwartzBruhat G) (x : G), ρ g f x = f (g⁻¹ * x)) ∧
      Continuous (fun p : G × SchwartzBruhat G => ρ p.1 p.2) ∧
      ∀ K : Set G, IsCompact K → ∀ U ∈ 𝓝 (0 : SchwartzBruhat G),
        ∃ V ∈ 𝓝 (0 : SchwartzBruhat G), ∀ g ∈ K, ∀ f ∈ V, ρ g f ∈ U := by
  obtain ⟨ι, _, p, hp⟩ := (schwartzBruhat_main_structure G).1.1
  have : IsTopologicalAddGroup (SchwartzBruhat G) := hp.topologicalAddGroup
  have : ContinuousSMul ℂ (SchwartzBruhat G) := hp.continuousSMul
  exact ⟨fun g f => Sol_MasulloGRH_schwartzBruhat_translation_continuous.ρ g f,
    fun g f x => rfl, joint hp, fun K hK U hU => equicont hp K hK U hU⟩
