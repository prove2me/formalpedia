-- Prove2me | solution 1 for GlobalTheory.exists_integral_of_local_presentation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:49.218664+00:00
-- url     : https://prove2.me/submissions/a34e497d-5a40-4b3e-b197-93df0493ac69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetNotMemSpanMulVecOfSocle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIntegralOfLocalPresentationPow
import Theorems.Thm_GlobalTheory_exists_pow_mul_one_sub_mem_map_maximalIdeal
import Theorems.Thm_GlobalTheory_exists_mul_kills_ker_of_localization
import Theorems.Thm_GlobalTheory_det_notMem_span_mulVec_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O H : Type) [CommRing O] [IsLocalRing O] [CommRing H] [Algebra O H] [Module.Finite O H] (ε : H →ₐ[O] O) (g n : ℕ) (T : Type) [CommRing T] [Algebra H T] [Algebra O T] [IsScalarTower O H T] [IsLocalization.AtPrime T ((IsLocalRing.maximalIdeal O).comap ε)] (εT : T →ₐ[O] O), (∀ h, εT (algebraMap H T h) = ε h) → ∀ (S : Type) [CommRing S] [Algebra O S] (π : S →ₐ[O] T) (x : Fin g → S) (a : Matrix (Fin g) (Fin g) S) (ρ : S →+* MvPowerSeries (Fin g) (IsLocalRing.ResidueField O)), Function.Surjective π → RingHom.ker π = Ideal.span (Set.range (a.mulVec x)) → RingHom.ker εT = Ideal.span (Set.range fun i => π (x i)) → (∀ i j, εT (π (a i j)) = if i = j then (n : O) else 0) → (∀ i, ρ (x i) = MvPowerSeries.X i) → (∀ c ∈ IsLocalRing.maximalIdeal O, ρ (algebraMap O S c) = 0) → ∃ l : H, (∀ h, ε h = 0 → h * l = 0) ∧ (n : O) ^ g ∣ ε l ∧ l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H) := by
  intro O H _ _ _ _ _ ε g n T _ _ _ _ _ εT hε S _ _ π x a ρ hπ hker hkerT ha hρx hρm
  classical
  set m := IsLocalRing.maximalIdeal O with hm
  set p : Ideal H := m.comap ε with hp
  have hmT : (m.map (algebraMap O H)).map (algebraMap H T) = m.map (algebraMap O T) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hmS : (m.map (algebraMap O S)).map (π : S →+* T) = m.map (algebraMap O T) := by
    rw [Ideal.map_map, AlgHom.comp_algebraMap]
  set A : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) (IsLocalRing.ResidueField O)) :=
    ρ.mapMatrix a with hA
  have hred : ∀ z : S, π z ∈ m.map (algebraMap O T) →
      ρ z ∈ Ideal.span (Set.range (A.mulVec MvPowerSeries.X)) := by
    intro z hz
    rw [← hmS] at hz
    have hz' : z ∈ m.map (algebraMap O S) ⊔ RingHom.ker π := by
      have := Ideal.comap_map_of_surjective (π : S →+* T) hπ (m.map (algebraMap O S))
      have h2 : z ∈ ((m.map (algebraMap O S)).map (π : S →+* T)).comap (π : S →+* T) := hz
      rw [this] at h2
      exact h2
    have hle : m.map (algebraMap O S) ⊔ RingHom.ker π ≤
        (Ideal.span (Set.range (A.mulVec MvPowerSeries.X))).comap ρ := by
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro c hc
        simp only [Ideal.mem_comap, hρm c hc, zero_mem]
      · rw [hker, Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        refine Ideal.subset_span ⟨i, ?_⟩
        simp [hA, Matrix.mulVec, dotProduct, hρx]
    exact hle hz'
  have hx0 : ∀ i, εT (π (x i)) = 0 := fun i => by
    have : π (x i) ∈ RingHom.ker εT := by rw [hkerT]; exact Ideal.subset_span ⟨i, rfl⟩
    exact this
  have hnil : ∀ i, ∃ N : ℕ, π (x i) ^ N ∈ m.map (algebraMap O T) := by
    intro i
    obtain ⟨⟨u, t⟩, hut⟩ := IsLocalization.surj p.primeCompl (π (x i))
    have hu : ε u = 0 := by
      have := congrArg εT hut
      rw [map_mul, hx0, zero_mul, hε] at this
      exact this.symm
    obtain ⟨N, y, hy⟩ := exists_pow_mul_one_sub_mem_map_maximalIdeal O H u
    have hy' := Ideal.mem_map_of_mem (algebraMap H T) hy
    rw [hmT, map_mul, map_pow] at hy'
    have hunit : IsUnit (algebraMap H T (1 - y * u)) := by
      refine IsLocalization.map_units T (⟨1 - y * u, ?_⟩ : p.primeCompl)
      intro hc
      have hc' : ε (1 - y * u) ∈ m := hc
      rw [map_sub, map_mul, hu, mul_zero, sub_zero, map_one] at hc'
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 hc')
    rw [Ideal.mul_unit_mem_iff_mem _ hunit] at hy'
    simp only at hut
    rw [← hut, mul_pow,
      Ideal.mul_unit_mem_iff_mem _ ((IsLocalization.map_units T t).pow N)] at hy'
    exact ⟨N, hy'⟩
  choose N hN using hnil
  have hdet : π a.det ∉ m.map (algebraMap O T) := by
    intro hc
    refine det_notMem_span_mulVec_X _ g (Finset.univ.sup N) A (fun i => ?_) ?_
    · rw [← hρx, ← map_pow]
      apply hred
      rw [map_pow]
      exact Ideal.pow_mem_of_pow_mem _ (hN i) (Finset.le_sup (Finset.mem_univ i))
    · rw [hA, ← RingHom.map_det]
      exact hred _ hc
  have hkill : ∀ w : T, εT w = 0 → w * π a.det = 0 := by
    intro w hw
    have hw' : w ∈ RingHom.ker εT := hw
    rw [hkerT] at hw'
    have hle : Ideal.span (Set.range fun i => π (x i)) ≤
        LinearMap.ker (LinearMap.mulRight T (π a.det)) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      change π (x i) * π a.det = 0
      rw [← map_mul]
      change x i * a.det ∈ RingHom.ker π
      have h1 : x i * a.det = (a.adjugate.mulVec (a.mulVec x)) i := by
        rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
        simp [mul_comm]
      rw [h1, hker]
      change ∑ j, a.adjugate i j * a.mulVec x j ∈ _
      exact Ideal.sum_mem _ fun j _ =>
        Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self j))
    exact hle hw'
  have hval : εT (π a.det) = (n : O) ^ g := by
    have h1 : εT (π a.det) = ((εT.comp π).mapMatrix a).det := by
      rw [← AlgHom.map_det]; rfl
    have h2 : (εT.comp π).mapMatrix a = Matrix.diagonal fun _ => (n : O) := by
      ext i j
      simp [Matrix.diagonal_apply, ha]
    rw [h1, h2, Matrix.det_diagonal]
    simp
  obtain ⟨⟨u, t⟩, hut⟩ := IsLocalization.surj p.primeCompl (π a.det)
  simp only at hut
  obtain ⟨s, hs⟩ := exists_mul_kills_ker_of_localization O H ε p.primeCompl T u (fun h hh => by
    rw [map_mul, ← hut, ← mul_assoc, hkill _ (by rw [hε, hh]), zero_mul])
  refine ⟨s * u, hs, ?_, fun hc => hdet ?_⟩
  · have := congrArg εT hut
    rw [map_mul, hval, hε, hε] at this
    rw [map_mul, ← this]
    exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
  · have hc' := Ideal.mem_map_of_mem (algebraMap H T) hc
    rw [hmT, map_mul, Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units T s), ← hut,
      Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units T t)] at hc'
    exact hc'
end GlobalTheory
