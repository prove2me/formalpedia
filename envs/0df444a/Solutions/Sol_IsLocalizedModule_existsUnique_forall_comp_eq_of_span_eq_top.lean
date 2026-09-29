-- Prove2me | solution 1 for IsLocalizedModule.existsUnique_forall_comp_eq_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/0199f32e-273d-510d-a658-47b58d60352d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalizedModule_existsUnique_forall_comp_eq_of_span_eq_top

set_option autoImplicit false

universe u

namespace MorphismDescentAux

theorem pow_sup_eq {B : Type u} [CommRing B] {ι : Type*} [Fintype ι] (b : B) (n : ι → ℕ) (i : ι) :
    b ^ (Finset.univ.sup n) = b ^ (Finset.univ.sup n - n i) * b ^ (n i) := by
  rw [← pow_add, Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ i))]

theorem exists_sum_mul_pow_eq_one {B : Type u} [CommRing B] {k : ℕ} (f : Fin k → B)
    (hf : Ideal.span (Set.range f) = ⊤) (n : Fin k → ℕ) : ∃ c : Fin k → B, ∑ i, c i * f i ^ n i = 1 := by
  classical
  let m : ℕ := Finset.univ.sup n
  have htop : Ideal.span (Set.range fun i => f i ^ m) = ⊤ := by
    have := Ideal.span_pow_eq_top (Set.range f) hf m
    rwa [← Set.range_comp] at this
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).1
    (htop.symm ▸ Submodule.mem_top : (1 : B) ∈ Ideal.span (Set.range fun i => f i ^ m))
  refine ⟨fun i => c i * f i ^ (m - n i), ?_⟩
  rw [← hc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, ← pow_sup_eq (f i) n i]

end MorphismDescentAux

open MorphismDescentAux in
theorem solution
    {B : Type u} [CommRing B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (M : Fin k → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)]
    (M₂ : Fin k → Fin k → Type u) [∀ i j, AddCommGroup (M₂ i j)] [∀ i j, Module B (M₂ i j)]
    (ρl : ∀ i j, M i →ₗ[B] M₂ i j) (ρr : ∀ i j, M j →ₗ[B] M₂ i j)
    (hρr : ∀ i j, IsLocalizedModule (Submonoid.powers (f i)) (ρr i j))
    (N : Type u) [AddCommGroup N] [Module B N] (π : ∀ i, N →ₗ[B] M i)
    (hπ : ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (π i))
    (hπc : ∀ i j, ρl i j ∘ₗ π i = ρr i j ∘ₗ π j)
    (T : Type u) [AddCommGroup T] [Module B T] (g : ∀ i, T →ₗ[B] M i)
    (hg : ∀ i j, ρl i j ∘ₗ g i = ρr i j ∘ₗ g j) :
    ∃! G : T →ₗ[B] N, ∀ i, π i ∘ₗ G = g i := by
  classical

  have hinj : ∀ n : N, (∀ i, π i n = 0) → n = 0 := by
    intro n hn
    have h1 : ∀ i, ∃ a : ℕ, f i ^ a • n = 0 := by
      intro i
      have : π i n = π i 0 := by rw [hn i, map_zero]
      obtain ⟨c, hc⟩ := (hπ i).exists_of_eq this
      obtain ⟨a, ha⟩ := (Submonoid.mem_powers_iff _ _).1 c.2
      exact ⟨a, by rw [Submonoid.smul_def, Submonoid.smul_def, ← ha, smul_zero] at hc; exact hc⟩
    choose a ha using h1
    obtain ⟨c, hc⟩ := exists_sum_mul_pow_eq_one f hf a
    calc n = (∑ i, c i * f i ^ a i) • n := by rw [hc, one_smul]
      _ = ∑ i, c i • (f i ^ a i • n) := by rw [Finset.sum_smul]; simp only [mul_smul]
      _ = 0 := by simp only [ha, smul_zero, Finset.sum_const_zero]

  have hexists : ∀ m : ∀ i, M i, (∀ i j, ρl i j (m i) = ρr i j (m j)) → ∃ n : N, ∀ i, π i n = m i := by
    intro m hm

    have h1 : ∀ i, ∃ (p : N × ℕ), ∀ j, π j p.1 = f i ^ p.2 • m j := by
      intro i
      obtain ⟨⟨n₀, s⟩, hs⟩ := (hπ i).surj (m i)
      obtain ⟨a, ha⟩ := (Submonoid.mem_powers_iff _ _).1 s.2
      have hs' : π i n₀ = f i ^ a • m i := by rw [← hs, Submonoid.smul_def, ← ha]

      have h2 : ∀ j, ∃ b : ℕ, f i ^ b • π j n₀ = f i ^ b • (f i ^ a • m j) := by
        intro j
        have : ρr i j (π j n₀) = ρr i j (f i ^ a • m j) := by
          rw [← LinearMap.comp_apply, ← hπc, LinearMap.comp_apply, hs', map_smul, map_smul, hm i j]
        obtain ⟨c, hc⟩ := (hρr i j).exists_of_eq this
        obtain ⟨b, hb⟩ := (Submonoid.mem_powers_iff _ _).1 c.2
        exact ⟨b, by rw [Submonoid.smul_def, Submonoid.smul_def, ← hb] at hc; exact hc⟩
      choose b hb using h2
      let bm : ℕ := Finset.univ.sup b
      refine ⟨(f i ^ bm • n₀, bm + a), fun j => ?_⟩
      rw [map_smul, pow_sup_eq (f i) b j, mul_smul, hb j, ← mul_smul, ← mul_smul, ← pow_sup_eq (f i) b j, ← pow_add]
    choose p hp using h1
    obtain ⟨c, hc⟩ := exists_sum_mul_pow_eq_one f hf (fun i => (p i).2)
    refine ⟨∑ i, c i • (p i).1, fun j => ?_⟩
    rw [map_sum]
    simp only [map_smul, hp]
    calc ∑ i, c i • (f i ^ (p i).2 • m j) = (∑ i, c i * f i ^ (p i).2) • m j := by
          rw [Finset.sum_smul]; simp only [mul_smul]
      _ = m j := by rw [hc, one_smul]

  choose lift hlift using hexists
  have hgc : ∀ (t : T) i j, ρl i j (g i t) = ρr i j (g j t) := fun t i j => by
    rw [← LinearMap.comp_apply, hg, LinearMap.comp_apply]
  let Gfun : T → N := fun t => lift (fun i => g i t) (hgc t)
  have hG : ∀ t i, π i (Gfun t) = g i t := fun t i => hlift _ _ i
  have hadd : ∀ t t', Gfun (t + t') = Gfun t + Gfun t' := by
    intro t t'
    rw [← sub_eq_zero]
    apply hinj
    intro i
    rw [map_sub, map_add, hG, hG, hG, map_add, sub_self]
  have hsmul : ∀ (r : B) t, Gfun (r • t) = r • Gfun t := by
    intro r t
    rw [← sub_eq_zero]
    apply hinj
    intro i
    rw [map_sub, map_smul, hG, hG, map_smul, sub_self]
  let G : T →ₗ[B] N := { toFun := Gfun, map_add' := hadd, map_smul' := hsmul }
  refine ⟨G, fun i => LinearMap.ext fun t => hG t i, fun G' hG' => ?_⟩
  apply LinearMap.ext
  intro t
  rw [← sub_eq_zero]
  apply hinj
  intro i
  rw [map_sub, sub_eq_zero, ← LinearMap.comp_apply, hG' i]
  exact (hG t i).symm

end S_IsLocalizedModule_existsUnique_forall_comp_eq_of_span_eq_top
end P2MW
export P2MW.S_IsLocalizedModule_existsUnique_forall_comp_eq_of_span_eq_top (solution)
