-- Prove2me | solution 1 for MasulloGRH.expDecaySchwartz_exists_stages
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T18:22:09.804884+00:00
-- url     : https://prove2.me/submissions/c3fdb48d-1808-47b0-9b85-523f9335f58a

import Theorems.Thm_MasulloGRH_expDecay_exists_cofinal_goodSubgroups
import Theorems.Thm_MasulloGRH_expDecayStage_frechet_nuclear
import Theorems.Thm_MasulloGRH_expDecayStage_exists_retraction
import Theorems.Thm_MasulloGRH_expDecayStage_transition
import Theorems.Thm_MasulloGRH_expDecaySchwartz_exists_good_invariant

set_option autoImplicit false

universe u

namespace MasulloGRHStSkAux

lemma cont_comp_expl {α β γ : Type*} (tα : TopologicalSpace α) (tβ : TopologicalSpace β)
    (tγ : TopologicalSpace γ) {g : β → γ} {f : α → β} (hg : @Continuous β γ tβ tγ g)
    (hf : @Continuous α β tα tβ f) : @Continuous α γ tα tγ (g ∘ f) := hg.comp hf

end MasulloGRHStSkAux

open MasulloGRH MasulloGRHStSkAux in
theorem solution
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) :
    ∃ (F : ℕ → Type u) (_ : ∀ N, AddCommGroup (F N)) (_ : ∀ N, Module ℂ (F N))
      (_ : ∀ N, TopologicalSpace (F N))
      (J : (N : ℕ) → F N →ₗ[ℂ] ExpDecaySchwartz G m I)
      (P : (N : ℕ) → ExpDecaySchwartz G m I →ₗ[ℂ] F N),
      (∀ N, IsFrechet (F N) ∧ IsNuclear (F N)) ∧
      (∀ N, Continuous (J N)) ∧ (∀ N, Continuous (P N)) ∧
      (∀ N y, P N (J N y) = y) ∧
      (∀ N M, N ≤ M → LinearMap.range (J N) ≤ LinearMap.range (J M)) ∧
      (∀ x : ExpDecaySchwartz G m I, ∃ N, x ∈ LinearMap.range (J N)) ∧
      (inferInstance : TopologicalSpace (ExpDecaySchwartz G m I)) =
        sInf {t | IsLocallyConvexTopology (ExpDecaySchwartz G m I) t ∧
          ∀ N, @Continuous (F N) (ExpDecaySchwartz G m I) _ t (J N)} := by
  obtain ⟨k, hkg, hka, hkc⟩ := expDecay_exists_cofinal_goodSubgroups G m hm
  choose P hPc hPJ using fun N =>
    expDecayStage_exists_retraction G m hm I hI hne (k N) (hkg N)
  have hJc : ∀ N, Continuous (ExpDecayStage.incl G m I (k N)) := fun N =>
    continuous_sInf_rng.2 fun _ ht => ht.2 (k N) (hkg N)
  have hrange : ∀ N, LinearMap.range (ExpDecayStage.incl G m I (k N)) =
      expDecayInvSubmodule G m I (k N) := fun N => Submodule.range_subtype _
  refine ⟨fun N => ExpDecayStage G m I (k N), fun N => inferInstance, fun N => inferInstance,
    fun N => inferInstance, fun N => ExpDecayStage.incl G m I (k N), P,
    fun N => expDecayStage_frechet_nuclear G m hm I hI hne (k N) (hkg N), hJc, hPc, hPJ,
    ?_, ?_, ?_⟩
  · intro N M h
    rw [hrange, hrange]
    intro ϕ hϕ hh hhk g
    exact hϕ hh (hka h hhk) g
  · intro x
    obtain ⟨k', hk', hx⟩ := expDecaySchwartz_exists_good_invariant G m hm I hI hne x
    obtain ⟨N, hN⟩ := hkc k' hk'
    refine ⟨N, ?_⟩
    rw [hrange]
    intro hh hhk g
    exact hx hh (hN hhk) g
  · have hf : ∀ k' : Subgroup G, IsGoodSubgroup k' → ∃ N,
        ∃ f : ExpDecayStage G m I k' → ExpDecayStage G m I (k N), Continuous f ∧
          ∀ y, ExpDecayStage.incl G m I (k N) (f y) = ExpDecayStage.incl G m I k' y := by
      intro k' hk'
      obtain ⟨N, hN⟩ := hkc k' hk'
      exact ⟨N, expDecayStage_transition G m hm I hI hne k' (k N) hk' (hkg N) hN⟩
    show sInf _ = _
    congr 1
    ext t
    refine and_congr_right fun _ => ⟨fun h N => h (k N) (hkg N), fun h k' hk' => ?_⟩
    obtain ⟨N, f, hfc, hfe⟩ := hf k' hk'
    have e : (Subtype.val : ExpDecayStage G m I k' → ExpDecaySchwartz G m I) =
        ExpDecayStage.incl G m I (k N) ∘ f := funext fun y => (hfe y).symm
    have := cont_comp_expl _ _ _ (h N) hfc
    rw [← e] at this
    exact this
