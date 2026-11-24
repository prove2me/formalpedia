-- Prove2me | solution 1 for GlobalTheory.lattice_hom_finite_image_of_trivial_on_multiples
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:14:47.349093+00:00
-- url     : https://prove2.me/submissions/63190fb6-6ce8-46a9-9fdd-125bf77147ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeHomFiniteImageOfTrivialOnMultiples

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (G : Type) [Group G] (e : (Fin g → ℂ) → G) (N : ℕ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z w, e (z + w) = e z * e w) → 0 < N →
    (∀ l ∈ Λ, e ((N : ℂ) • l) = 1) → (e '' (Λ : Set (Fin g → ℂ))).Finite := by
  intro g Λ G _ e N hd hspan hadd hN hker
  haveI := hd
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  let b := Module.Free.chooseBasis ℤ Λ
  let f : (Module.Free.ChooseBasisIndex ℤ Λ → Fin N) → G :=
    fun a => e (∑ i, ((a i : ℕ) : ℤ) • ((b i : Λ) : Fin g → ℂ))
  refine (Set.finite_range f).subset ?_
  rintro _ ⟨l, hl, rfl⟩
  set x : Λ := ⟨l, hl⟩ with hxdef
  let c : Module.Free.ChooseBasisIndex ℤ Λ → ℤ := fun i => b.repr x i
  let q : Λ := ∑ i, (c i / N) • b i
  have hc : ∀ i, 0 ≤ c i % (N : ℤ) := fun i => Int.emod_nonneg _ (by exact_mod_cast hN.ne')
  refine ⟨fun i => ⟨(c i % (N : ℤ)).toNat, ?_⟩, ?_⟩
  · have h1 := Int.emod_lt_of_pos (c i) (by exact_mod_cast hN : (0 : ℤ) < N)
    omega
  · have hl' : l = (N : ℂ) • ((q : Λ) : Fin g → ℂ) +
        ∑ i, (((c i % (N : ℤ)).toNat : ℕ) : ℤ) • ((b i : Λ) : Fin g → ℂ) := by
      have hx : l = ((∑ i, c i • b i : Λ) : Fin g → ℂ) := by
        rw [b.sum_repr x]
      rw [hx]
      simp only [q, Submodule.coe_sum, Submodule.coe_smul, Finset.smul_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Int.toNat_of_nonneg (hc i)]
      have hN' : (N : ℂ) = ((N : ℤ) : ℂ) := by norm_cast
      rw [hN', Int.cast_smul_eq_zsmul, smul_smul, ← add_smul]
      have h2 := Int.mul_ediv_add_emod (c i) (N : ℤ)
      congr 1
      linarith
    refine Eq.trans ?_ (congrArg e hl').symm
    rw [hadd, hker _ q.2, one_mul]
end GlobalTheory
