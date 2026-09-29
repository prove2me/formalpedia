-- Prove2me | solution 1 for Module.Finite.of_isAdicComplete_of_isHausdorff_of_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/ce109e08-c3bd-58bd-b7e0-fb57f2480778

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Finite_of_isAdicComplete_of_isHausdorff_of_quotient

set_option autoImplicit false

universe u v

theorem solution
    {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type v) [AddCommGroup M] [Module R M] [IsHausdorff I M]
    (h : Module.Finite R (M ⧸ (I • ⊤ : Submodule R M))) :
    Module.Finite R M := by
  classical

  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin (R := R) (M := M ⧸ (I • ⊤ : Submodule R M))
  choose s hs using fun i => Submodule.mkQ_surjective (I • ⊤ : Submodule R M) (f i)
  set N : Submodule R M := Submodule.span R (Set.range s) with hN
  have hNsup : N ⊔ I • ⊤ = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : (I • ⊤ : Submodule R M).mkQ x ∈ Submodule.map (I • ⊤ : Submodule R M).mkQ N := by
      rw [hN, Submodule.map_span, ← Set.range_comp]
      have : ((I • ⊤ : Submodule R M).mkQ ∘ s) = f := funext hs
      rw [this, hf]
      exact Submodule.mem_top
    have hx' : x ∈ Submodule.comap (I • ⊤ : Submodule R M).mkQ (Submodule.map (I • ⊤ : Submodule R M).mkQ N) :=
      hx
    rwa [Submodule.comap_map_eq, Submodule.ker_mkQ] at hx'

  have hstep : ∀ (k : ℕ) (y : M), y ∈ I ^ k • (⊤ : Submodule R M) →
      ∃ a : Fin n → R, (∀ i, a i ∈ I ^ k) ∧ y - ∑ i, a i • s i ∈ I ^ (k + 1) • (⊤ : Submodule R M) := by
    intro k y hy
    have hdec : I ^ k • (⊤ : Submodule R M) = I ^ k • N ⊔ I ^ (k + 1) • (⊤ : Submodule R M) := by
      conv_lhs => rw [← hNsup, Submodule.smul_sup, ← Submodule.smul_assoc, Ideal.smul_eq_mul, ← pow_succ]
    rw [hdec, Submodule.mem_sup] at hy
    obtain ⟨u, hu, w, hw, rfl⟩ := hy
    rw [hN, Submodule.mem_ideal_smul_span_iff_exists_sum] at hu
    obtain ⟨a, ha, rfl⟩ := hu
    refine ⟨a, ha, ?_⟩
    rw [Finsupp.sum_fintype _ _ (fun i => zero_smul R (s i)), add_sub_cancel_left]
    exact hw
  choose a ha using hstep

  suffices htop : ∀ x : M, x ∈ N by
    have hT : (⊤ : Submodule R M) = N := eq_top_iff.mpr (fun x _ => htop x) |>.symm
    rw [Module.finite_def, hT, hN]
    exact Submodule.fg_span (Set.finite_range s)
  intro x

  let seq : (k : ℕ) → {y : M // y ∈ I ^ k • (⊤ : Submodule R M)} :=
    fun k => Nat.rec ⟨x, by rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; exact Submodule.mem_top⟩
      (fun k y => ⟨y.1 - ∑ i, a k y.1 y.2 i • s i, (ha k y.1 y.2).2⟩) k
  let A : ℕ → Fin n → R := fun k => a k (seq k).1 (seq k).2
  have hA : ∀ k i, A k i ∈ I ^ k := fun k i => (ha k (seq k).1 (seq k).2).1 i
  have hseq : ∀ k, (seq (k + 1)).1 = (seq k).1 - ∑ i, A k i • s i := fun k => rfl

  let c : ℕ → Fin n → R := fun k i => ∑ j ∈ Finset.range k, A j i
  have hc : ∀ k, x - ∑ i, c k i • s i = (seq k).1 := by
    intro k
    induction k with
    | zero => simp [c]; rfl
    | succ k ih =>
      rw [hseq, ← ih]
      simp only [c, Finset.sum_range_succ, add_smul, Finset.sum_add_distrib]
      abel

  have hmemR : ∀ (m : ℕ) (r : R), r ∈ I ^ m → r ∈ (I ^ m • ⊤ : Submodule R R) := fun m r hr => by
    simpa only [smul_eq_mul, mul_one] using
      Submodule.smul_mem_smul hr (Submodule.mem_top : (1 : R) ∈ (⊤ : Submodule R R))
  have hleR : ∀ m : ℕ, (I ^ m • ⊤ : Submodule R R) ≤ (I ^ m : Ideal R) := fun m =>
    Submodule.smul_le.mpr fun r hr t _ => by rw [smul_eq_mul]; exact Ideal.mul_mem_right _ _ hr
  have hcauchy : ∀ i, ∀ {m n' : ℕ}, m ≤ n' → c m i ≡ c n' i [SMOD (I ^ m • ⊤ : Submodule R R)] := by
    intro i m n' hmn
    rw [SModEq.sub_mem]
    refine hmemR m _ ?_
    have : c m i - c n' i = -∑ j ∈ Finset.Ico m n', A j i := by
      simp only [c]
      rw [← Finset.sum_range_add_sum_Ico _ hmn]
      abel
    rw [this]
    exact Submodule.neg_mem _ (Ideal.sum_mem _ fun j hj =>
      Ideal.pow_le_pow_right (Finset.mem_Ico.mp hj).1 (hA j i))
  choose L hL using fun i => IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete (I := I) (R := R)) (hcauchy i)

  have hlim : ∀ k, x - ∑ i, L i • s i ∈ I ^ k • (⊤ : Submodule R M) := by
    intro k
    have hsplit : x - ∑ i, L i • s i = (x - ∑ i, c k i • s i) + ∑ i, (c k i - L i) • s i := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      abel
    rw [hsplit, hc]
    refine Submodule.add_mem _ (seq k).2 (Submodule.sum_mem _ fun i _ => ?_)
    refine Submodule.smul_mem_smul (hleR k ?_) Submodule.mem_top
    exact (SModEq.sub_mem.mp (hL i k))
  have hzero : x - ∑ i, L i • s i = 0 :=
    IsHausdorff.haus ‹IsHausdorff I M› _ fun k => by
      rw [SModEq.sub_mem, sub_zero]
      exact hlim k
  rw [sub_eq_zero] at hzero
  rw [hzero, hN]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end S_Module_Finite_of_isAdicComplete_of_isHausdorff_of_quotient
end P2MW
export P2MW.S_Module_Finite_of_isAdicComplete_of_isHausdorff_of_quotient (solution)
