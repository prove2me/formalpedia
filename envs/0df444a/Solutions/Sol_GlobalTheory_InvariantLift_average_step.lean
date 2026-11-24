-- Prove2me | solution 1 for GlobalTheory.InvariantLift.average_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:54:00.503245+00:00
-- url     : https://prove2.me/submissions/e5a69099-7087-4a7f-bda0-4d06a16e52ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInvariantMatrixLiftOfAdicComplete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InvariantLift
variable {G : Type} [Group G] {A : Type} [CommRing A] {r : ℕ}
namespace GlobalTheory.InvariantLift
theorem _root_.solution (σ : G → A →+* A) (hσ : ∀ g h a, σ (g * h) a = σ g (σ h a))
    (M : G →* Matrix (Fin r) (Fin r) A) (hM : ∀ g h i j, σ g (M h i j) = M h i j)
    (N : Subgroup G) [hN : N.Normal] [Finite (G ⧸ N)] (τ : A) (hτ : ∀ g ∈ N, σ g τ = τ)
    (hτ1 : ∑ᶠ x : G ⧸ N, σ x.out τ = 1) (c d : A) (hd : ∀ g ∈ N, ∀ i j, d ∣ (M g - 1) i j)
    (W : Matrix (Fin r) (Fin r) A) (hW : ∀ g ∈ N, W.map (σ g) = W)
    (hc : ∀ g i j, c ∣ (M g * W.map (σ g) - W) i j) :
    ∃ W' : Matrix (Fin r) (Fin r) A, (∀ i j, c ∣ (W - W') i j) ∧ (∀ g ∈ N, W'.map (σ g) = W') ∧
      ∀ g i j, d ∣ (M g * W'.map (σ g) - W') i j := by
  classical
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _

  have dl : ∀ (e : A) (X : Matrix (Fin r) (Fin r) A), (∀ i j, e ∣ X i j) →
      ∀ (Y : Matrix (Fin r) (Fin r) A) i j, e ∣ (X * Y) i j := by
    intro e X hX Y i j
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun k _ => (hX i k).mul_right _
  have dr : ∀ (e : A) (Y : Matrix (Fin r) (Fin r) A), (∀ i j, e ∣ Y i j) →
      ∀ (X : Matrix (Fin r) (Fin r) A) i j, e ∣ (X * Y) i j := by
    intro e Y hY X i j
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun k _ => (hY k j).mul_left _

  have hfix : ∀ a : A, (∀ m ∈ N, σ m a = a) → ∀ g, ∀ n ∈ N, σ n (σ g a) = σ g a := by
    intro a ha g n hn
    have hm : g⁻¹ * n * g ∈ N := by simpa using hN.conj_mem n hn g⁻¹
    rw [← hσ, show n * g = g * (g⁻¹ * n * g) by group, hσ, ha _ hm]
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin r) (Fin r) A, U = τ • W := ⟨_, rfl⟩
  have hUfix : ∀ m ∈ N, ∀ k l, σ m (U k l) = U k l := by
    intro m hm k l
    have hWe : σ m (W k l) = W k l := congrFun (congrFun (hW m hm) k) l
    rw [hU, Matrix.smul_apply, smul_eq_mul, map_mul, hτ m hm, hWe]
  have hUl : ∀ g, ∀ n ∈ N, U.map (σ (n * g)) = U.map (σ g) := by
    intro g n hn
    ext k l
    simp only [Matrix.map_apply, hσ]
    exact hfix _ (fun m hm => hUfix m hm k l) g n hn
  have hUr : ∀ g, ∀ n ∈ N, U.map (σ (g * n)) = U.map (σ g) := by
    intro g n hn
    ext k l
    simp only [Matrix.map_apply, hσ, hUfix n hn]
  have hMfix : ∀ g h, (M h).map (σ g) = M h := by
    intro g h
    ext i j
    exact hM g h i j
  have hUmap : ∀ g h, (U.map (σ h)).map (σ g) = U.map (σ (g * h)) := by
    intro g h
    ext i j
    simp [hσ]
  have hsum : ∀ (f : A →+* A) (X : G ⧸ N → Matrix (Fin r) (Fin r) A),
      (∑ x, X x).map f = ∑ x, (X x).map f := by
    intro f X
    ext i j
    simp [Matrix.sum_apply, map_sum]

  refine ⟨∑ x : G ⧸ N, M x.out * U.map (σ x.out), ?_, ?_, ?_⟩
  · intro i j
    have h1 : ∑ x : G ⧸ N, σ x.out τ = 1 := by
      rw [← finsum_eq_sum_of_fintype]
      exact hτ1
    have hent : ∀ x : G ⧸ N, (M x.out * U.map (σ x.out)) i j =
        σ x.out τ * (M x.out * W.map (σ x.out)) i j := by
      intro x
      simp only [hU, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hsplit : (W - ∑ x : G ⧸ N, M x.out * U.map (σ x.out)) i j =
        ∑ x : G ⧸ N, σ x.out τ * (W i j - (M x.out * W.map (σ x.out)) i j) := by
      rw [Matrix.sub_apply, Matrix.sum_apply, Finset.sum_congr rfl (fun x _ => hent x)]
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]
    rw [hsplit]
    refine Finset.dvd_sum fun x _ => dvd_mul_of_dvd_right ?_ _
    exact dvd_sub_comm.mp (by simpa only [Matrix.sub_apply] using hc x.out i j)
  · intro n hn
    rw [hsum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.map_mul, hMfix, hUmap, hUl _ n hn]
  · intro g i j
    have hmul : M g * (∑ x : G ⧸ N, M x.out * U.map (σ x.out)).map (σ g) =
        ∑ x : G ⧸ N, M (g * x.out) * U.map (σ (g * x.out)) := by
      rw [hsum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.map_mul, hMfix, hUmap, map_mul, mul_assoc]
    have hre : ∑ x : G ⧸ N, M x.out * U.map (σ x.out) =
        ∑ x : G ⧸ N, M (g • x).out * U.map (σ (g • x).out) :=
      (Equiv.sum_comp (MulAction.toPerm g) (fun y : G ⧸ N => M y.out * U.map (σ y.out))).symm
    rw [hmul, hre, ← Finset.sum_sub_distrib, Matrix.sum_apply]
    refine Finset.dvd_sum fun x _ => ?_
    obtain ⟨n, hn, hgx⟩ : ∃ n ∈ N, g * x.out = (g • x).out * n := by
      refine ⟨((g • x).out)⁻¹ * (g * x.out), ?_, (mul_inv_cancel_left _ _).symm⟩
      rw [← QuotientGroup.eq]
      simp only [QuotientGroup.out_eq']
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      simp only [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.mk_mul, QuotientGroup.out_eq',
        Quotient.out_eq]
    rw [hgx, map_mul, hUr _ n hn]
    have hfac : M (g • x).out * M n * U.map (σ (g • x).out) - M (g • x).out * U.map (σ (g • x).out)
        = M (g • x).out * ((M n - 1) * U.map (σ (g • x).out)) := by
      noncomm_ring
    rw [hfac]
    exact dr d _ (dl d _ (fun i' j' => by simpa [Matrix.sub_apply] using hd n hn i' j') _) _ i j
end GlobalTheory.InvariantLift
