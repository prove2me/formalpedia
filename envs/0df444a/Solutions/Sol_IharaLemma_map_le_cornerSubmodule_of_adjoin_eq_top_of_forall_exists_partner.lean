-- Prove2me | solution 1 for IharaLemma.map_le_cornerSubmodule_of_adjoin_eq_top_of_forall_exists_partner
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/2a794be1-1144-5c3e-a31f-d7b3582a937a

import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Definitions.Def_IharaLemma_IdempotentSplitting
import Theorems.Thm_IharaLemma_map_le_cornerSubmodule_of_forall_ne_exists_intertwining
import Theorems.Thm_IharaLemma_exists_pow_smul_corner_mem_maximalIdeal_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaLemma_map_le_cornerSubmodule_of_adjoin_eq_top_of_forall_exists_partner

set_option autoImplicit false

namespace CohL2
namespace Link1

open IsLocalRing IharaLemma

theorem algebraMap_mem_of_mem_maximalIdeal {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {B : Type} [CommRing B] [Algebra 𝒪 B] [Module.Finite 𝒪 B]
    (J : Ideal B) [hJ : J.IsMaximal] {a : 𝒪} (ha : a ∈ maximalIdeal 𝒪) : algebraMap 𝒪 B a ∈ J := by
  have hmax : (J.comap (algebraMap 𝒪 B)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal J
  have heq : J.comap (algebraMap 𝒪 B) = maximalIdeal 𝒪 := IsLocalRing.eq_maximalIdeal hmax
  have : a ∈ J.comap (algebraMap 𝒪 B) := heq ▸ ha
  exact this

theorem eq_of_forall_gen_sub_mem {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {B : Type} [CommRing B] [Algebra 𝒪 B] [Module.Finite 𝒪 B]
    (S : IdempotentSplitting B) (i j : Fin S.n) (G : Set B) (hG : Algebra.adjoin 𝒪 G = ⊤)
    (hc : ∀ g ∈ G, ∃ c : 𝒪, g - algebraMap 𝒪 B c ∈ S.𝔪 i ∧ g - algebraMap 𝒪 B c ∈ S.𝔪 j) :
    i = j := by

  have hall : ∀ x : B, ∃ a : 𝒪, x - algebraMap 𝒪 B a ∈ S.𝔪 i ⊓ S.𝔪 j := by
    intro x
    have hx : x ∈ Algebra.adjoin 𝒪 G := hG ▸ Algebra.mem_top
    refine Algebra.adjoin_induction (p := fun y _ => ∃ a : 𝒪, y - algebraMap 𝒪 B a ∈ S.𝔪 i ⊓ S.𝔪 j)
      ?_ ?_ ?_ ?_ hx
    · intro g hg
      obtain ⟨c, h1, h2⟩ := hc g hg
      exact ⟨c, h1, h2⟩
    · intro r
      exact ⟨r, by rw [sub_self]; exact Ideal.zero_mem _⟩
    · rintro x y - - ⟨a, ha⟩ ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      have : x + y - algebraMap 𝒪 B (a + b) = (x - algebraMap 𝒪 B a) + (y - algebraMap 𝒪 B b) := by
        rw [map_add]; ring
      rw [this]
      exact Ideal.add_mem _ ha hb
    · rintro x y - - ⟨a, ha⟩ ⟨b, hb⟩
      refine ⟨a * b, ?_⟩
      have : x * y - algebraMap 𝒪 B (a * b) =
          x * (y - algebraMap 𝒪 B b) + (x - algebraMap 𝒪 B a) * algebraMap 𝒪 B b := by
        rw [map_mul]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hb) (Ideal.mul_mem_right _ _ ha)

  have hle : S.𝔪 i ≤ S.𝔪 j := by
    intro x hx
    obtain ⟨a, ha⟩ := hall x
    by_cases hau : a ∈ maximalIdeal 𝒪
    · have h1 : algebraMap 𝒪 B a ∈ S.𝔪 j := algebraMap_mem_of_mem_maximalIdeal (S.𝔪 j) hau
      have := Ideal.add_mem _ ha.2 h1
      rwa [sub_add_cancel] at this
    · exfalso
      have hu : IsUnit a := of_not_not fun h => hau ((IsLocalRing.mem_maximalIdeal a).mpr h)
      have hmem : algebraMap 𝒪 B a ∈ S.𝔪 i := by
        have := Ideal.sub_mem _ hx ha.1
        rwa [sub_sub_cancel] at this
      exact (S.isMaximal i).ne_top (Ideal.eq_top_of_isUnit_mem _ hmem (hu.map _))
  have heq : S.𝔪 i = S.𝔪 j := ((S.isMaximal i).eq_of_le (S.isMaximal j).ne_top hle)
  exact S.𝔪_injective heq

theorem corner_transport {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {B B' : Type} [CommRing B] [CommRing B'] [Algebra 𝒪 B] [Algebra 𝒪 B']
    [Module.Finite 𝒪 B] [Module.Finite 𝒪 B']
    {V V' : Type} [AddCommGroup V] [Module 𝒪 V] [Module B V] [IsScalarTower 𝒪 B V]
    [AddCommGroup V'] [Module 𝒪 V'] [Module B' V'] [IsScalarTower 𝒪 B' V']
    (f : V →ₗ[𝒪] V') (S : IdempotentSplitting B) (i : Fin S.n)
    (S' : IdempotentSplitting B') (i' : Fin S'.n)
    (hsep : ∀ v' : V', (∀ k : ℕ, v' ∈ ((maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V')) → v' = 0)
    (G' : Set B') (hG' : Algebra.adjoin 𝒪 G' = ⊤)
    (hgen : ∀ g' ∈ G', ∃ (c : 𝒪) (g₀ : B), g' - algebraMap 𝒪 B' c ∈ S'.𝔪 i' ∧
      g₀ - algebraMap 𝒪 B c ∈ S.𝔪 i ∧ ∀ v : V, f (g₀ • v) = g' • f v) :
    ∀ w : V, w ∈ cornerSubmodule (M := V) (S.e i) → f w ∈ cornerSubmodule (M := V') (S'.e i') := by
  intro w hw
  refine IharaLemma.map_le_cornerSubmodule_of_forall_ne_exists_intertwining f S' i'
    ((cornerSubmodule (M := V) (S.e i)).restrictScalars 𝒪) (maximalIdeal 𝒪) hsep ?_ w hw
  intro j' hj'

  have hex : ∃ g' ∈ G', ∃ (c : 𝒪) (g₀ : B), g' - algebraMap 𝒪 B' c ∈ S'.𝔪 i' ∧
      g₀ - algebraMap 𝒪 B c ∈ S.𝔪 i ∧ (∀ v : V, f (g₀ • v) = g' • f v) ∧
      g' - algebraMap 𝒪 B' c ∉ S'.𝔪 j' := by
    by_contra hcon
    push Not at hcon
    apply hj'
    refine (eq_of_forall_gen_sub_mem S' i' j' G' hG' fun g' hg' => ?_).symm
    obtain ⟨c, g₀, h1, h2, h3⟩ := hgen g' hg'
    exact ⟨c, h1, hcon g' hg' c g₀ h1 h2 h3⟩
  obtain ⟨g', -, c, g₀, -, hg₀, hfg, hnot⟩ := hex
  set b : B := g₀ - algebraMap 𝒪 B c with hb
  let g : V →ₗ[𝒪] V :=
    { toFun := fun v => b • v
      map_add' := fun x y => smul_add b x y
      map_smul' := fun r v => smul_comm b r v }
  have hg : ∀ v, g v = b • v := fun _ => rfl
  refine ⟨g, g' - algebraMap 𝒪 B' c, hnot, ?_, ?_, ?_⟩
  · intro v
    rw [hg, hb, sub_smul, map_sub, hfg, algebraMap_smul, map_smul, sub_smul, algebraMap_smul]
  · intro v hv
    rw [hg]
    exact Submodule.smul_mem _ b hv
  · intro k
    obtain ⟨n, hn⟩ := IharaLemma.exists_pow_smul_corner_mem_maximalIdeal_smul (𝒪 := 𝒪) S i b hg₀ (V := V) k
    refine ⟨n, fun v hv => ?_⟩
    have hpow : ∀ (n : ℕ) (m : V), (g ^ n) m = (b ^ n) • m := by
      intro n
      induction n with
      | zero => intro m; simp
      | succ n ih =>
        intro m
        rw [pow_succ, Module.End.mul_apply, hg, ih, smul_smul, ← pow_succ]
    rw [hpow]
    exact hn v hv

end CohL2.Link1

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {B B' : Type} [CommRing B] [CommRing B'] [Algebra 𝒪 B] [Algebra 𝒪 B']
    [Module.Finite 𝒪 B] [Module.Finite 𝒪 B']
    {V V' : Type} [AddCommGroup V] [Module 𝒪 V] [Module B V] [IsScalarTower 𝒪 B V]
    [AddCommGroup V'] [Module 𝒪 V'] [Module B' V'] [IsScalarTower 𝒪 B' V']
    (f : V →ₗ[𝒪] V') (S : IharaLemma.IdempotentSplitting B) (i : Fin S.n)
    (S' : IharaLemma.IdempotentSplitting B') (i' : Fin S'.n)
    (hsep : ∀ v' : V', (∀ k : ℕ, v' ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V')) → v' = 0)
    (G' : Set B') (hG' : Algebra.adjoin 𝒪 G' = ⊤)
    (hgen : ∀ g' ∈ G', ∃ (c : 𝒪) (g₀ : B), g' - algebraMap 𝒪 B' c ∈ S'.𝔪 i' ∧
      g₀ - algebraMap 𝒪 B c ∈ S.𝔪 i ∧ ∀ v : V, f (g₀ • v) = g' • f v) :
    ∀ w ∈ IharaLemma.cornerSubmodule (M := V) (S.e i),
      f w ∈ IharaLemma.cornerSubmodule (M := V') (S'.e i') :=
  CohL2.Link1.corner_transport f S i S' i' hsep G' hG' hgen

end S_IharaLemma_map_le_cornerSubmodule_of_adjoin_eq_top_of_forall_exists_partner
end P2MW
export P2MW.S_IharaLemma_map_le_cornerSubmodule_of_adjoin_eq_top_of_forall_exists_partner (solution)
