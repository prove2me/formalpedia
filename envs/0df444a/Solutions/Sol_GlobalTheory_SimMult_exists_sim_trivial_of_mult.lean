-- Prove2me | solution 1 for GlobalTheory.SimMult.exists_sim_trivial_of_mult
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:00:12.097557+00:00
-- url     : https://prove2.me/submissions/468260ae-9e3e-4520-afe9-02c20f9a1d19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSimTrivialOfMult
import Theorems.Thm_GlobalTheory_SimMult_mem_of_mul_eq_span
import Theorems.Thm_GlobalTheory_SimMult_exists_scalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SimMult
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.SimMult
theorem _root_.solution :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (N : ℕ) (f : D.La →ₗ[𝓞 E] D.La) (ν : ℤ), 0 < N → IsCoprime ν (N : ℤ) → (∀ a b, (N : ℤ) ∣ D.EF (f a) (f b) - ν * D.EF a b) → ∃ g : Sim D, (∀ a, D.ModN N (g.f N a - f a)) ∧ (N : ℤ) ∣ g.ν N - ν) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (N : ℕ) (ν : ℤ), 0 < N → IsCoprime ν (N : ℤ) → (l.A : ℤ) ∣ ν - 1 → ∃ g : Sim D, (N : ℤ) ∣ g.ν N - ν ∧ (l.A : ℤ) ∣ g.ν l.A - 1 ∧ (∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) ∧ ∀ a, D.ModN l.A (g.f l.A a - a) := by
  intro hgrp hlift E _ _ _ H D l N ν hN hν hA
  have hMpos : 0 < l.M := by have := l.three_le; omega
  have hApos := l.A_pos
  by_cases hpq : 1 ≤ D.p + D.q
  swap
  · have := D.fin
    have := D.proj
    have : Subsingleton D.La := Module.finrank_zero_iff.1 (D.rank.trans (by norm_cast; omega))
    have hz : ∀ n x, D.ModN n x := fun n x => ⟨0, Subsingleton.elim _ _⟩
    refine ⟨⟨fun _ => LinearMap.id, fun _ => ν, fun _ _ _ _ _ => hz _ _,
      fun _ _ => ⟨LinearMap.id, fun _ => ⟨hz _ _, hz _ _⟩⟩, fun n _ a b => ?_⟩, by simp, hA,
      fun a => by rw [LinearMap.id_apply, sub_self]; exact Submodule.zero_mem _, fun a => hz _ _⟩
    rw [Subsingleton.elim a 0]; simp
  have hνA : IsCoprime ν (l.A : ℤ) := by
    obtain ⟨t, ht⟩ := hA
    exact ⟨1, -t, by linear_combination ht⟩
  obtain ⟨r, hr, hrp, hrν⟩ := Nat.forall_exists_prime_gt_and_zmodEq (N * l.M * l.A)
    (q := N * l.A) (a := ν) (by positivity) (by rw [Nat.cast_mul]; exact hν.mul_right hνA)
  have hn : 0 < N * l.M * l.A := by positivity
  have hrc : IsCoprime (r : ℤ) ((N * l.M * l.A : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hrp).2
      (Nat.not_dvd_of_pos_of_lt hn hr))
  have hd : ((N * l.A : ℕ) : ℤ) ∣ r - ν := hrν.symm.dvd
  have hdN : (N : ℤ) ∣ r - ν := dvd_trans (by push_cast; exact dvd_mul_right _ _) hd
  have hdA : (l.A : ℤ) ∣ r - 1 := by
    have h1 : (l.A : ℤ) ∣ r - ν := dvd_trans (by push_cast; exact dvd_mul_left _ _) hd
    simpa using dvd_add h1 hA
  obtain ⟨c, ⟨u, hu⟩, hcM, ⟨v, hv⟩⟩ := exists_scalar H l _ hn ⟨N * l.A, by ring⟩ ⟨N * l.M, by ring⟩
    r hrc hdA
  obtain ⟨g, hg, hgν⟩ := hlift E H D _ (c • LinearMap.id) r hn hrc (by
    intro a b
    refine ⟨D.EF a (u • b), ?_⟩
    have h1 : H.bar c • c • b = (r : ℤ) • b + ((N * l.M * l.A : ℕ) : ℤ) • u • b := by
      rw [← Int.cast_smul_eq_zsmul (𝓞 E), ← Int.cast_smul_eq_zsmul (𝓞 E), smul_smul, smul_smul,
        ← add_smul, Int.cast_natCast (N * l.M * l.A)]
      congr 1
      linear_combination hu
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [D.adj, h1, map_add, map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul]
    ring)
  have hνg : ∀ m k : ℕ, 0 < m → 0 < k → N * l.M * l.A = m * k → (m : ℤ) ∣ g.ν m - r := by
    intro m k hm hk h
    have h1 := ((hgrp E H D hpq).1 g m k hm hk).1
    rw [h] at hgν
    have h2 : (m : ℤ) ∣ g.ν (m * k) - r := dvd_trans (by push_cast; exact dvd_mul_right _ _) hgν
    simpa using dvd_sub h2 h1
  have hfg : ∀ m k : ℕ, 0 < m → 0 < k → N * l.M * l.A = m * k → ∀ a, ∃ b,
      g.f m a - a = (c - 1) • a + (m : 𝓞 E) • b := by
    intro m k hm hk h a
    obtain ⟨b₁, h1⟩ := g.tower m k hm hk a
    obtain ⟨b₂, h2⟩ := hg a
    rw [h] at h2
    refine ⟨k • b₂ - b₁, ?_⟩
    rw [Nat.cast_smul_eq_nsmul, smul_sub, smul_smul, ← h1, ← h2, sub_smul, one_smul]
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    abel
  refine ⟨g, ?_, ?_, fun a => ?_, fun a => ?_⟩
  · simpa using dvd_add (hνg N (l.M * l.A) hN (by positivity) (by ring)) hdN
  · simpa using dvd_add (hνg l.A (N * l.M) hApos (by positivity) (by ring)) hdA
  · obtain ⟨b, hb⟩ := hfg l.M (N * l.A) hMpos (by positivity) (by ring) a
    rw [hb]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul hcM Submodule.mem_top)
      (Submodule.smul_mem_smul
        (mem_of_mul_eq_span l.prod) Submodule.mem_top)
  · obtain ⟨b, hb⟩ := hfg l.A (N * l.M) hApos (by positivity) (by ring) a
    refine ⟨v • a + b, ?_⟩
    rw [hb, hv, ← Nat.cast_smul_eq_nsmul (𝓞 E), smul_add, smul_smul]
end GlobalTheory.SimMult
