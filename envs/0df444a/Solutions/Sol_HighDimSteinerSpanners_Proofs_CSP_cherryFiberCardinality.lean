-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.cherryFiberCardinality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:51:39.788853+00:00
-- url     : https://prove2.me/submissions/4690f5db-68b1-47a5-91b5-048ce1998bce

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.GCongr
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessMoments
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_CherryMoments
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_sphereFiberCardinality
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_powerset_card_le_bound


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution : ∀ {N q : ℕ} (C₁ r_star : ℕ), 3 ≤ C₁ →
    ∀ (x : Fin N → Fin q) (R_old : Finset (Fin N × Fin q)),
    R_old.card ≤ 21 * C₁ ^ 2 * r_star →
    ∀ (s : ℕ),
    ((Finset.univ.filter (fun y : Fin N → Fin q =>
      ((disagreeSet x y).filter (fun v => (v, y v) ∉ R_old)).card = s ∧
      dHam x y ≤ r_star)).card : ℝ) ≤
      ((r_star + 1 : ℕ) : ℝ) *
        (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
        ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s) := by
  intro N q C₁ r_star hC₁_loc x R_old hR_old s
  let Sph := Finset.univ.filter (fun g : Fin N → Fin q =>
    (∀ v ∉ (Finset.univ : Finset (Fin N)), g v = x v) ∧ dHam x g = s)
  let F_fresh := fun y : Fin N → Fin q => (disagreeSet x y).filter (fun v => (v, y v) ∉ R_old)
  let A_rev := fun y : Fin N → Fin q =>
    ((disagreeSet x y).filter (fun v => (v, y v) ∈ R_old)).image (fun v => (v, y v))
  let y_fresh := fun (y : Fin N → Fin q) (v : Fin N) => if v ∈ F_fresh y then y v else x v
  let Ψ := fun y : Fin N → Fin q => (A_rev y, y_fresh y)
  let P_old := R_old.powerset.filter (fun G => G.card ≤ r_star)
  have hle : (Finset.univ.filter (fun y : Fin N → Fin q =>
      (F_fresh y).card = s ∧ dHam x y ≤ r_star)).card ≤
      (P_old ×ˢ Sph).card := by
    apply Finset.card_le_card_of_injOn Ψ
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      rw [Finset.mem_coe, Finset.mem_product]
      refine ⟨?_, ?_⟩
      · simp only [P_old, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨?_, ?_⟩
        · intro vc hvc
          rcases Finset.mem_image.mp hvc with ⟨v, hv, rfl⟩
          exact (Finset.mem_filter.mp hv).2
        · exact le_trans Finset.card_image_le
            (le_trans (Finset.card_filter_le _ _) hy.2)
      · dsimp only [Sph]
        rw [Finset.mem_filter]
        have hdiff : disagreeSet x (y_fresh y) = F_fresh y := by
          ext v
          simp only [disagreeSet, y_fresh, F_fresh, Finset.mem_filter, Finset.mem_univ, true_and]
          split_ifs with hv
          · exact iff_of_true hv.1 hv
          · exact iff_of_false (not_not.mpr rfl) hv
        exact ⟨Finset.mem_univ _, fun v hv => absurd (Finset.mem_univ v) hv, by rw [dHam, hdiff,
            hy.1]⟩
    · intro y₁ _ y₂ _ heq
      rcases Prod.mk.inj heq with ⟨hA, hyf⟩
      have hnotA_eq : ∀ y : Fin N → Fin q, ∀ v : Fin N, (v, y v) ∉ A_rev y → y_fresh y v = y v := by
        intro y v hnotA
        dsimp only [y_fresh]
        by_cases hxy : x v = y v
        · have hnotF : v ∉ F_fresh y := by simp [F_fresh, disagreeSet, hxy]
          rw [if_neg hnotF, hxy]
        · have hnotR : (v, y v) ∉ R_old := by
            intro hR
            apply hnotA
            exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨by simp [disagreeSet, hxy],
                hR⟩, rfl⟩
          have hmemF : v ∈ F_fresh y := Finset.mem_filter.mpr ⟨by simp [disagreeSet, hxy], hnotR⟩
          exact if_pos hmemF
      funext v
      by_cases h1 : (v, y₁ v) ∈ A_rev y₁
      · rw [hA] at h1
        rcases Finset.mem_image.mp h1 with ⟨v', _, hp⟩
        rcases Prod.mk.inj hp with ⟨rfl, hy21⟩
        exact hy21.symm
      · by_cases h2 : (v, y₂ v) ∈ A_rev y₂
        · rw [← hA] at h2
          rcases Finset.mem_image.mp h2 with ⟨v', _, hp⟩
          rcases Prod.mk.inj hp with ⟨rfl, hy12⟩
          exact hy12
        · rw [← hnotA_eq y₁ v h1, ← hnotA_eq y₂ v h2, congr_fun hyf v]
  rw [Finset.card_product] at hle
  have hSph : Sph.card = N.choose s * (q - 1) ^ s := by
    have h := sphereFiberCardinality x Finset.univ s
    rwa [Finset.card_univ, Fintype.card_fin] at h
  rw [hSph] at hle
  have hle_r : ((Finset.univ.filter (fun y : Fin N → Fin q =>
      (F_fresh y).card = s ∧ dHam x y ≤ r_star)).card : ℝ) ≤
      (P_old.card : ℝ) * ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s) := by
    exact_mod_cast hle
  have hP_r : (P_old.card : ℝ) ≤
      ((r_star + 1 : ℕ) : ℝ) *
        (2 : ℝ) ^ (((2 * Nat.clog 2 C₁ + 6) * r_star : ℕ) : ℝ) :=
    powerset_card_le_bound R_old C₁ 21 r_star hC₁_loc (le_refl 21) hR_old
  have hexp_le : (2 : ℝ) ^ (((2 * Nat.clog 2 C₁ + 6) * r_star : ℕ) : ℝ) ≤
      (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h1 : 100 * ((2 * Nat.clog 2 C₁ + 6) * r_star) ≤ cspLam0 C₁ * r_star := by
      unfold cspLam0
      have hC1_ge1 : 1 ≤ C₁ := by omega
      have hm : 1 * (2 * Nat.clog 2 C₁ + 6) ≤ C₁ * (2 * Nat.clog 2 C₁ + 6) :=
        Nat.mul_le_mul_right _ hC1_ge1
      have h100 : 100 * (2 * Nat.clog 2 C₁ + 6) ≤ 100 * C₁ * (2 * Nat.clog 2 C₁ + 6) := by
        linarith only [hm]
      have hmr := Nat.mul_le_mul_right r_star h100
      rwa [Nat.mul_assoc 100 _ r_star] at hmr
    have h1r : ((100 * ((2 * Nat.clog 2 C₁ + 6) * r_star) : ℕ) : ℝ) ≤
        ((cspLam0 C₁ * r_star : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h1r ⊢
    linarith only [h1r]
  have hP_r2 : (P_old.card : ℝ) ≤
      ((r_star + 1 : ℕ) : ℝ) *
        (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) :=
    le_trans hP_r (mul_le_mul_of_nonneg_left hexp_le (Nat.cast_nonneg _))
  exact le_trans hle_r (mul_le_mul_of_nonneg_right hP_r2 (by positivity))
end HighDimSteinerSpanners.Proofs.CSP
