-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.freshCoordinateFiberCardinality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:50:37.549159+00:00
-- url     : https://prove2.me/submissions/e079b3c3-2182-4d6b-9257-a6b64f623d1e

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Calibration
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessMoments
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_powerset_card_le_bound


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution : ∀ {N q : ℕ} (C₁ r_star m : ℕ), 3 ≤ C₁ → m < cspKMom C₁ →
    ∀ (a b : Fin N → Fin q) (z_prev : Fin m → (Fin N → Fin q)),
    dHam a b ≤ C₁ * r_star →
    (∀ t : Fin m, dHam (z_prev t) a ≤ C₁ * r_star) →
    ∀ s : ℕ,
    ((Finset.univ.filter (fun x : Fin N → Fin q =>
      (candMFresh a b m z_prev x).card = s ∧ dHam x a ≤ C₁ * r_star)).card : ℝ) ≤
      ((C₁ * r_star + 1 : ℕ) : ℝ) *
        (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
        ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s) := by
  intro N q C₁ r_star m hC₁_loc hm_loc a b z_prev hd_ab_loc hz_prev s
  let R_old := cspRvc a b m z_prev
  let R_neq := R_old.filter (fun vc : Fin N × Fin q => vc.2 ≠ a vc.1)
  have hR_neq_card : R_neq.card ≤ (1 + m) * (C₁ * r_star) := by
    have hsub : R_neq ⊆ (disagreeSet a b).image (fun v => (v, b v)) ∪
        Finset.univ.biUnion (fun t : Fin m =>
          (disagreeSet (z_prev t) a).image (fun v => (v, z_prev t v))) := by
      intro vc hvc
      simp only [R_neq, R_old, cspRvc, Finset.mem_filter, Finset.mem_union,
        Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_biUnion] at hvc
      rcases hvc with ⟨(⟨v, rfl⟩ | ⟨v, rfl⟩) | ⟨t, v, rfl⟩, hne⟩
      · exact absurd rfl hne
      · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
          Finset.mem_univ, true_and, disagreeSet, Finset.mem_filter]
        exact Or.inl ⟨v, Ne.symm hne, rfl⟩
      · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
          Finset.mem_univ, true_and, disagreeSet, Finset.mem_filter]
        exact Or.inr ⟨t, v, hne, rfl⟩
    have hc1 := Finset.card_le_card hsub
    have hc2 := Finset.card_union_le
      ((disagreeSet a b).image (fun v => (v, b v)))
      (Finset.univ.biUnion (fun t : Fin m =>
        (disagreeSet (z_prev t) a).image (fun v => (v, z_prev t v))))
    have hc_ab : ((disagreeSet a b).image (fun v => (v, b v))).card ≤ C₁ * r_star :=
      le_trans Finset.card_image_le hd_ab_loc
    have hc_z : (Finset.univ.biUnion (fun t : Fin m =>
        (disagreeSet (z_prev t) a).image (fun v => (v, z_prev t v)))).card ≤
        m * (C₁ * r_star) := by
      calc
        (Finset.univ.biUnion (fun t : Fin m =>
            (disagreeSet (z_prev t) a).image (fun v => (v, z_prev t v)))).card
          ≤ ∑ t : Fin m, ((disagreeSet (z_prev t) a).image (fun v => (v, z_prev t v))).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _ : Fin m, (C₁ * r_star) :=
            Finset.sum_le_sum (fun t _ => le_trans Finset.card_image_le (hz_prev t))
        _ = m * (C₁ * r_star) := by rw [Finset.sum_const, Finset.card_fin, smul_eq_mul]
    have h_add : C₁ * r_star + m * (C₁ * r_star) = (1 + m) * (C₁ * r_star) := by ring
    omega
  have hR_neq_20 : R_neq.card ≤ 20 * C₁ ^ 2 * (C₁ * r_star) := by
    have h1m : 1 + m ≤ 20 * C₁ ^ 2 := by
      unfold cspKMom at hm_loc
      omega
    exact le_trans hR_neq_card (Nat.mul_le_mul_right (C₁ * r_star) h1m)
  let Sphere_a : Finset (Fin N → Fin q) :=
    ((Finset.univ : Finset (Fin N)).powersetCard s).biUnion (fun S =>
      Fintype.piFinset (fun v : Fin N =>
        if v ∈ S then (Finset.univ : Finset (Fin q)).erase (a v) else {a v}))
  have hSphere_card : Sphere_a.card ≤ N.choose s * (q - 1) ^ s := by
    calc
      Sphere_a.card
        ≤ ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard s,
            (Fintype.piFinset (fun v : Fin N =>
              if v ∈ S then (Finset.univ : Finset (Fin q)).erase (a v) else {a v})).card :=
          Finset.card_biUnion_le
      _ = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard s, (q - 1) ^ s := by
          refine Finset.sum_congr rfl (fun S hS => ?_)
          have hS_card : S.card = s := (Finset.mem_powersetCard.mp hS).2
          rw [Fintype.card_piFinset]
          have hfac : ∀ v ∈ (Finset.univ : Finset (Fin N)),
              (if v ∈ S then (Finset.univ : Finset (Fin q)).erase (a v) else {a v}).card =
                if v ∈ S then q - 1 else 1 := by
            intro v _
            split_ifs
            · rw [Finset.card_erase_of_mem (Finset.mem_univ (a v)), Finset.card_fin]
            · exact Finset.card_singleton _
          rw [Finset.prod_congr rfl hfac, Finset.prod_ite]
          have hfilt : (Finset.univ : Finset (Fin N)).filter (fun v => v ∈ S) = S := by
            ext v; simp
          rw [hfilt, Finset.prod_const, hS_card, Finset.prod_const_one, mul_one]
      _ = N.choose s * (q - 1) ^ s := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_fin, smul_eq_mul]
  let G_of : (Fin N → Fin q) → Finset (Fin N × Fin q) :=
    fun x =>
      (Finset.univ.filter (fun v : Fin N => v ∉ candMFresh a b m z_prev x ∧ x v ≠ a v)).image
        (fun v => (v, x v))
  let y_of : (Fin N → Fin q) → (Fin N → Fin q) :=
    fun x v => if v ∈ candMFresh a b m z_prev x then x v else a v
  have hy_fresh : ∀ x : Fin N → Fin q,
      candMFresh a b m z_prev x = Finset.univ.filter (fun v : Fin N => y_of x v ≠ a v) := by
    intro x
    ext v
    simp only [candMFresh, y_of, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hv
      rw [if_pos (by simpa [candMFresh] using hv)]
      intro heq
      apply hv
      rw [heq]
      simp only [cspRvc, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inl (Or.inl ⟨v, rfl⟩)
    · intro hne
      by_contra hnot
      simp [hnot] at hne
  have hG_mem_iff : ∀ (x : Fin N → Fin q) (v : Fin N),
      v ∉ candMFresh a b m z_prev x →
      ∀ c : Fin q, (v, c) ∈ G_of x ↔ c = x v ∧ x v ≠ a v := by
    intro x v hv c
    simp only [G_of, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
    constructor
    · rintro ⟨v', ⟨_, hne⟩, rfl, rfl⟩
      exact ⟨rfl, hne⟩
    · rintro ⟨rfl, hne⟩
      exact ⟨v, ⟨hv, hne⟩, rfl, rfl⟩
  let P_old := R_neq.powerset.filter (fun G => G.card ≤ C₁ * r_star)
  have hFib_le : (Finset.univ.filter (fun x : Fin N → Fin q =>
      (candMFresh a b m z_prev x).card = s ∧ dHam x a ≤ C₁ * r_star)).card ≤
      (P_old ×ˢ Sphere_a).card := by
    apply Finset.card_le_card_of_injOn (fun x => (G_of x, y_of x))
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [P_old, Finset.mem_coe, Finset.mem_product, Finset.mem_filter,
        Finset.mem_powerset]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro vc hvc
        rcases Finset.mem_image.mp hvc with ⟨v, hv, rfl⟩
        simp only [candMFresh, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hv
        simp only [R_neq, R_old, Finset.mem_filter]
        exact ⟨hv.1, hv.2⟩
      · have hsub_da : Finset.univ.filter
            (fun v : Fin N => v ∉ candMFresh a b m z_prev x ∧ x v ≠ a v) ⊆ disagreeSet x a := by
          intro v hv
          simp only [disagreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          exact hv.2
        exact le_trans Finset.card_image_le (le_trans (Finset.card_le_card hsub_da) hx.2)
      · simp only [Sphere_a, Finset.mem_biUnion, Finset.mem_powersetCard,
          Fintype.mem_piFinset]
        refine ⟨candMFresh a b m z_prev x, ⟨Finset.subset_univ _, hx.1⟩, ?_⟩
        intro v
        dsimp [y_of]
        split_ifs with hv
        · rw [Finset.mem_erase]
          refine ⟨?_, Finset.mem_univ _⟩
          intro heq
          simp only [candMFresh, Finset.mem_filter, Finset.mem_univ, true_and] at hv
          apply hv
          rw [heq]
          simp only [cspRvc, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
          exact Or.inl (Or.inl ⟨v, rfl⟩)
        · exact Finset.mem_singleton_self _
    · intro x₁ _ x₂ _ heq
      rcases Prod.mk.inj heq with ⟨hG_eq, hy_eq⟩
      have hS_eq : candMFresh a b m z_prev x₁ = candMFresh a b m z_prev x₂ := by
        rw [hy_fresh x₁, hy_fresh x₂, hy_eq]
      funext v
      by_cases hv : v ∈ candMFresh a b m z_prev x₁
      · have hv₂ : v ∈ candMFresh a b m z_prev x₂ := hS_eq ▸ hv
        have hy_v := congr_fun hy_eq v
        simpa [y_of, if_pos hv, if_pos hv₂] using hy_v
      · have hv₂ : v ∉ candMFresh a b m z_prev x₂ := hS_eq ▸ hv
        by_cases hx₁_ne : x₁ v ≠ a v
        · have hmem₁ : (v, x₁ v) ∈ G_of x₁ := (hG_mem_iff x₁ v hv (x₁ v)).mpr ⟨rfl, hx₁_ne⟩
          rw [hG_eq] at hmem₁
          exact ((hG_mem_iff x₂ v hv₂ (x₁ v)).mp hmem₁).1
        · push Not at hx₁_ne
          by_contra hx₂_ne
          have hx₂_ne_a : x₂ v ≠ a v := fun h => hx₂_ne (hx₁_ne.trans h.symm)
          have hmem₂ : (v, x₂ v) ∈ G_of x₂ := (hG_mem_iff x₂ v hv₂ (x₂ v)).mpr ⟨rfl, hx₂_ne_a⟩
          rw [← hG_eq] at hmem₂
          have heq₁₂ := ((hG_mem_iff x₁ v hv (x₂ v)).mp hmem₂).1
          exact hx₂_ne heq₁₂.symm
  rw [Finset.card_product] at hFib_le
  have hFib_nat := le_trans hFib_le (Nat.mul_le_mul_left P_old.card hSphere_card)
  have hFib_r : ((Finset.univ.filter (fun x : Fin N → Fin q =>
      (candMFresh a b m z_prev x).card = s ∧ dHam x a ≤ C₁ * r_star)).card : ℝ) ≤
      (P_old.card : ℝ) * ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s) := by
    exact_mod_cast hFib_nat
  have hP_old_r : (P_old.card : ℝ) ≤
      ((C₁ * r_star + 1 : ℕ) : ℝ) *
        (2 : ℝ) ^ (((2 * Nat.clog 2 C₁ + 6) * (C₁ * r_star) : ℕ) : ℝ) :=
    powerset_card_le_bound R_neq C₁ 20 (C₁ * r_star) hC₁_loc (by omega) hR_neq_20
  have hexp_eq : (((2 * Nat.clog 2 C₁ + 6) * (C₁ * r_star) : ℕ) : ℝ) =
      (1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) := by
    unfold cspLam0
    push_cast
    ring
  rw [hexp_eq] at hP_old_r
  exact le_trans hFib_r (mul_le_mul_of_nonneg_right hP_old_r (by positivity))
end HighDimSteinerSpanners.Proofs.CSP
