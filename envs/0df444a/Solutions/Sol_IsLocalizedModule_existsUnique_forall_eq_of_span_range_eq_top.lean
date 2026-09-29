-- Prove2me | solution 1 for IsLocalizedModule.existsUnique_forall_eq_of_span_range_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/64fafd2e-0189-5610-aedc-f5e752c2b1e9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalizedModule_existsUnique_forall_eq_of_span_range_eq_top

set_option autoImplicit false

namespace ModuleGlue

theorem exists_sum_mul_pow_eq_one {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (g : ι → R)
    (hg : Ideal.span (Set.range g) = ⊤) (N : ℕ) : ∃ a : ι → R, ∑ i, a i * g i ^ N = 1 := by
  classical
  have h : Ideal.span (Set.range fun i => g i ^ N) = ⊤ := by
    have := Ideal.span_pow_eq_top (Set.range g) hg N
    rw [← Set.range_comp] at this
    exact this
  have h1 : (1 : R) ∈ Ideal.span (Set.range fun i => g i ^ N) := by rw [h]; trivial
  rw [Ideal.mem_span_range_iff_exists_fun] at h1
  exact h1

end ModuleGlue

theorem solution
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} [Finite ι] (g : ι → R) (hg : Ideal.span (Set.range g) = ⊤)
    {Mi : ι → Type*} [∀ i, AddCommGroup (Mi i)] [∀ i, Module R (Mi i)]
    (fi : ∀ i, M →ₗ[R] Mi i) [∀ i, IsLocalizedModule (Submonoid.powers (g i)) (fi i)]
    {Mij : ι → ι → Type*} [∀ i j, AddCommGroup (Mij i j)] [∀ i j, Module R (Mij i j)]
    (fij : ∀ i j, M →ₗ[R] Mij i j) [∀ i j, IsLocalizedModule (Submonoid.powers (g i * g j)) (fij i j)]
    (ρ : ∀ i j, Mi i →ₗ[R] Mij i j) (ρ' : ∀ i j, Mi j →ₗ[R] Mij i j)
    (hρ : ∀ i j, (ρ i j).comp (fi i) = fij i j) (hρ' : ∀ i j, (ρ' i j).comp (fi j) = fij i j)
    (m : ∀ i, Mi i) (hm : ∀ i j, ρ i j (m i) = ρ' i j (m j)) :
    ∃! x : M, ∀ i, fi i x = m i := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι

  have huniq : ∀ x : M, (∀ i, fi i x = 0) → x = 0 := by
    intro x hx
    have hpow : ∀ i, ∃ n : ℕ, g i ^ n • x = 0 := by
      intro i
      obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (g i)) (f := fi i)).mp (hx i)
      obtain ⟨n, rfl⟩ := hs
      exact ⟨n, hsx⟩
    choose n hn using hpow
    let N := Finset.univ.sup n
    have hN : ∀ i, g i ^ N • x = 0 := by
      intro i
      have hle : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
      rw [← Nat.add_sub_cancel' hle, pow_add, mul_comm, mul_smul, hn i, smul_zero]
    obtain ⟨a, ha⟩ := ModuleGlue.exists_sum_mul_pow_eq_one g hg N
    calc x = (∑ i, a i * g i ^ N) • x := by rw [ha, one_smul]
      _ = ∑ i, a i • (g i ^ N • x) := by rw [Finset.sum_smul]; simp only [mul_smul]
      _ = 0 := by simp only [hN, smul_zero, Finset.sum_const_zero]
  refine existsUnique_of_exists_of_unique ?_ ?_
  swap
  · intro x y hx hy
    rw [← sub_eq_zero]
    apply huniq
    intro i
    rw [map_sub, hx i, hy i, sub_self]

  have hnum : ∀ i, ∃ (n : ℕ) (x : M), g i ^ n • m i = fi i x := by
    intro i
    obtain ⟨⟨x, ⟨s, hs⟩⟩, hxs⟩ := IsLocalizedModule.surj (Submonoid.powers (g i)) (fi i) (m i)
    obtain ⟨n, rfl⟩ := hs
    exact ⟨n, x, hxs⟩
  choose n x hx using hnum
  let N := Finset.univ.sup n
  have hxN : ∀ i, g i ^ N • m i = fi i (g i ^ (N - n i) • x i) := by
    intro i
    have hle : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
    rw [map_smul, ← hx i, ← mul_smul, ← pow_add, Nat.sub_add_cancel hle]

  obtain ⟨y, hyN⟩ : ∃ y : ∀ i, M, ∀ i, g i ^ N • m i = fi i (y i) := ⟨fun i => g i ^ (N - n i) • x i, hxN⟩
  clear hxN hx x

  have hcomp : ∀ i j, ∃ k : ℕ, (g i * g j) ^ k • (g j ^ N • y i - g i ^ N • y j) = 0 := by
    intro i j
    have e1 : fij i j (y i) = ρ i j (fi i (y i)) := by rw [← hρ i j]; rfl
    have e2 : fij i j (y j) = ρ' i j (fi j (y j)) := by rw [← hρ' i j]; rfl
    have h1 : fij i j (g j ^ N • y i - g i ^ N • y j) = 0 := by
      rw [map_sub, map_smul, map_smul, e1, e2, ← hyN i, ← hyN j, map_smul, map_smul, hm i j, smul_smul,
        smul_smul, mul_comm, sub_self]
    obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (g i * g j)) (f := fij i j)).mp h1
    obtain ⟨k, rfl⟩ := hs
    exact ⟨k, hsx⟩
  choose k hk using hcomp
  let K := Finset.univ.sup fun p : ι × ι => k p.1 p.2
  have hK : ∀ i j, (g i * g j) ^ K • (g j ^ N • y i - g i ^ N • y j) = 0 := by
    intro i j
    have hle : k i j ≤ K := Finset.le_sup (f := fun p : ι × ι => k p.1 p.2) (Finset.mem_univ (i, j))
    rw [← Nat.add_sub_cancel' hle, pow_add, mul_comm, mul_smul, hk i j, smul_zero]

  obtain ⟨z, hzL, hzz⟩ : ∃ z : ∀ i, M, (∀ i, g i ^ (N + K) • m i = fi i (z i)) ∧
      ∀ i j, g j ^ (N + K) • z i = g i ^ (N + K) • z j := by
    refine ⟨fun i => g i ^ K • y i, fun i => ?_, fun i j => ?_⟩
    · rw [map_smul, ← hyN i, ← mul_smul, ← pow_add, add_comm]
    · have := hK i j
      rw [smul_sub, sub_eq_zero, smul_smul, smul_smul] at this
      rw [smul_smul, smul_smul, show g j ^ (N + K) * g i ^ K = (g i * g j) ^ K * g j ^ N by ring,
        show g i ^ (N + K) * g j ^ K = (g i * g j) ^ K * g i ^ N by ring]
      exact this

  obtain ⟨a, ha⟩ := ModuleGlue.exists_sum_mul_pow_eq_one g hg (N + K)
  refine ⟨∑ i, a i • z i, fun j => ?_⟩

  have hsum : g j ^ (N + K) • ∑ i, a i • z i = z j := by
    rw [Finset.smul_sum]
    calc ∑ i, g j ^ (N + K) • (a i • z i) = ∑ i, a i • (g i ^ (N + K) • z j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_comm, hzz i j]
      _ = (∑ i, a i * g i ^ (N + K)) • z j := by rw [Finset.sum_smul]; simp only [mul_smul]
      _ = z j := by rw [ha, one_smul]

  have h2 : g j ^ (N + K) • fi j (∑ i, a i • z i) = g j ^ (N + K) • m j := by
    rw [← map_smul, hsum, hzL j]
  obtain ⟨u, hu⟩ := IsLocalizedModule.map_units (fi j) (⟨g j ^ (N + K), N + K, rfl⟩ : Submonoid.powers (g j))
  have h3 : ∀ w : Mi j, (u : Module.End R (Mi j)) w = g j ^ (N + K) • w := fun w => by
    rw [hu]; rfl
  have h4 : (u : Module.End R (Mi j)) (fi j (∑ i, a i • z i)) = (u : Module.End R (Mi j)) (m j) := by
    rw [h3, h3]; exact h2
  have h5 : ∀ w : Mi j, ((u⁻¹ : (Module.End R (Mi j))ˣ) : Module.End R (Mi j)) ((u : Module.End R (Mi j)) w) = w :=
    fun w => by rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
  calc fi j (∑ i, a i • z i)
      = ((u⁻¹ : (Module.End R (Mi j))ˣ) : Module.End R (Mi j)) ((u : Module.End R (Mi j)) (fi j (∑ i, a i • z i))) :=
        (h5 _).symm
    _ = ((u⁻¹ : (Module.End R (Mi j))ˣ) : Module.End R (Mi j)) ((u : Module.End R (Mi j)) (m j)) := by rw [h4]
    _ = m j := h5 _

end S_IsLocalizedModule_existsUnique_forall_eq_of_span_range_eq_top
end P2MW
export P2MW.S_IsLocalizedModule_existsUnique_forall_eq_of_span_range_eq_top (solution)
