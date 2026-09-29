-- Prove2me | solution 1 for GroupCohomology.RepPi.nonempty_tateHneg1_obj_linearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f659b116-a9b6-512a-927a-a6bb7a294620

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_RepPi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GroupCohomology_RepPi_nonempty_tateHneg1_obj_linearEquiv

set_option autoImplicit false
universe u
open CategoryTheory Rep

set_option maxHeartbeats 3200000

theorem solution {k G ι : Type u} [CommRing k] [Group G] [Fintype G]
    (F : ι → Rep.{u} k G) :
    Nonempty ((GroupCohomology.RepPi.obj F).tateHneg1 ≃ₗ[k] ((i : ι) → (F i).tateHneg1)) := by

  classical
  let P : Rep.{u} k G := GroupCohomology.RepPi.obj F
  have hnorm : ∀ (x : P) (i : ι), (P.ρ.norm x) i = (F i).ρ.norm (x i) := by
    intro x i
    simp only [Representation.norm, LinearMap.sum_apply]
    rw [Finset.sum_apply]
    rfl

  have hker : ∀ {W : Type u} [AddCommGroup W] [Module k W] (σ : Representation k G W) (x : W),
      x ∈ Representation.Coinvariants.ker σ → ∃ w : G → W, x = ∑ g, (σ g (w g) - w g) := by
    intro W _ _ σ x hx
    refine Submodule.span_induction ?_ ⟨0, by simp⟩ ?_ ?_ hx
    · rintro _ ⟨⟨g, v⟩, rfl⟩
      refine ⟨Pi.single g v, ?_⟩
      rw [Finset.sum_eq_single g]
      · simp
      · intro h _ hne; simp [Pi.single_eq_of_ne hne]
      · intro h; exact absurd (Finset.mem_univ g) h
    · rintro a b - - ⟨wa, rfl⟩ ⟨wb, rfl⟩
      exact ⟨wa + wb, by simp [Finset.sum_add_distrib, map_add]; abel⟩
    · rintro c a - ⟨w, rfl⟩
      exact ⟨c • w, by simp [Finset.smul_sum, smul_sub, map_smul]⟩

  let cC : P.ρ.Coinvariants →ₗ[k] ((i : ι) → (F i).ρ.Coinvariants) :=
    Representation.Coinvariants.lift P.ρ (LinearMap.pi fun i => Representation.Coinvariants.mk (F i).ρ ∘ₗ LinearMap.proj i)
      (fun g => LinearMap.ext fun x => funext fun i => by
        change Representation.Coinvariants.mk (F i).ρ ((P.ρ g x) i) = Representation.Coinvariants.mk (F i).ρ (x i)
        exact Representation.Coinvariants.mk_self_apply (F i).ρ g (x i))
  have hcC : ∀ (x : P) (i : ι), cC (Representation.Coinvariants.mk P.ρ x) i = Representation.Coinvariants.mk (F i).ρ (x i) :=
    fun x i => rfl

  have hmem : ∀ (c : P.tateHneg1) (i : ι), cC (c : P.ρ.Coinvariants) i ∈ LinearMap.ker (F i).ρ.normBar := by
    intro c i
    obtain ⟨x, hx⟩ := Representation.Coinvariants.mk_surjective P.ρ (c : P.ρ.Coinvariants)
    rw [LinearMap.mem_ker, ← hx, hcC]
    apply Subtype.ext
    rw [Representation.normBar_mk, Representation.coe_normToInvariants_apply]
    have h0 := c.2
    rw [LinearMap.mem_ker, ← hx, Representation.normBar_mk] at h0
    have h1 := congrArg (fun z : P.ρ.invariants => (z : P) i) h0
    simp only [Representation.coe_normToInvariants_apply] at h1
    rw [hnorm] at h1
    exact h1
  let Ψ : P.tateHneg1 →ₗ[k] ((i : ι) → (F i).tateHneg1) :=
    LinearMap.pi fun i => LinearMap.codRestrict _ (LinearMap.proj i ∘ₗ cC ∘ₗ (LinearMap.ker P.ρ.normBar).subtype) (fun c => hmem c i)
  have hΨ : ∀ (c : P.tateHneg1) (i : ι), ((Ψ c i : (F i).tateHneg1) : (F i).ρ.Coinvariants) = cC (c : P.ρ.Coinvariants) i :=
    fun c i => rfl
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    apply Subtype.ext
    obtain ⟨x, hx⟩ := Representation.Coinvariants.mk_surjective P.ρ (c : P.ρ.Coinvariants)
    have hxi : ∀ i, x i ∈ Representation.Coinvariants.ker (F i).ρ := fun i => by
      have h1 := congrArg (fun t => ((t i : (F i).tateHneg1) : (F i).ρ.Coinvariants)) hc
      simp only [hΨ, ← hx, hcC] at h1
      exact (Representation.Coinvariants.mk_eq_zero _).1 h1
    choose w hw using fun i => hker (F i).ρ (x i) (hxi i)
    change (c : P.ρ.Coinvariants) = 0
    rw [← hx]
    apply (Representation.Coinvariants.mk_eq_zero _).2
    have : x = ∑ g, (P.ρ g (fun i => w i g) - fun i => w i g) := by
      funext i
      rw [hw i, Finset.sum_apply]
      rfl
    rw [this]
    exact Submodule.sum_mem _ fun g _ => Representation.Coinvariants.sub_mem_ker g _
  have hsurj : Function.Surjective Ψ := fun t => by
    have hti : ∀ i, ∃ x : F i, Representation.Coinvariants.mk (F i).ρ x = ((t i : (F i).tateHneg1) : (F i).ρ.Coinvariants) :=
      fun i => Representation.Coinvariants.mk_surjective _ _
    choose x hx using hti
    have hmemP : Representation.Coinvariants.mk P.ρ (fun i => x i) ∈ LinearMap.ker P.ρ.normBar := by
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      rw [Representation.normBar_mk, Representation.coe_normToInvariants_apply]
      funext i
      rw [hnorm]
      have h0 := (t i).2
      rw [LinearMap.mem_ker, ← hx, Representation.normBar_mk] at h0
      have h1 := congrArg Subtype.val h0
      rw [Representation.coe_normToInvariants_apply] at h1
      exact h1
    refine ⟨⟨_, hmemP⟩, ?_⟩
    funext i
    apply Subtype.ext
    rw [hΨ]
    change cC (Representation.Coinvariants.mk P.ρ (fun i => x i)) i = _
    rw [hcC, hx]
  exact ⟨LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩⟩

end S_GroupCohomology_RepPi_nonempty_tateHneg1_obj_linearEquiv
end P2MW
export P2MW.S_GroupCohomology_RepPi_nonempty_tateHneg1_obj_linearEquiv (solution)
