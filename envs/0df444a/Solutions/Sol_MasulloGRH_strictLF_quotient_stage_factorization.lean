-- Prove2me | solution 1 for MasulloGRH.strictLF_quotient_stage_factorization
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:53:14.180168+00:00
-- url     : https://prove2.me/submissions/c6acacd9-c57f-4bc0-bf59-4f9e69705c7e

import Theorems.Thm_MasulloGRH_frechet_countable_pullback_open_quotient
import Theorems.Thm_MasulloGRH_bounded_in_strict_frechet_stages

open MasulloGRH Set Topology

private theorem stage_factor {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (X : ℕ → Submodule ℂ E) (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n))
    (V : Submodule ℂ E) [T2Space (E ⧸ V)] (hF : IsFrechet F) (u : F →L[ℂ] (E ⧸ V)) :
    ∃ (k : ℕ) (v : F →L[ℂ] (X k ⧸ V.comap (X k).subtype)),
      ∀ y, Submodule.mapQ (V.comap (X k).subtype) V (X k).subtype le_rfl (v y) = u y := by
  classical
  let b (n : ℕ) := V.mkQ.comp (X n).subtype
  have hb (n : ℕ) : Continuous (b n) := V.continuous_mkQ.comp continuous_subtype_val
  have cover (g : E ⧸ V) : ∃ n, g ∈ range (b n) := by
    obtain ⟨x, rfl⟩ := V.mkQ_surjective g
    obtain ⟨n, hn⟩ := hexh x
    exact ⟨n, ⟨x, hn⟩, rfl⟩
  obtain ⟨k, hk⟩ := frechet_countable_pullback_open_quotient F hF (fun n => X n) hX
    (E ⧸ V) u.toLinearMap u.continuous b hb cover
  let W := V.comap (X k).subtype
  let j := W.mapQ V (X k).subtype le_rfl
  have hj : Function.Injective j := by
    apply LinearMap.ker_eq_bot.mp
    rw [show j.ker = W.map W.mkQ from Submodule.ker_mapQ ..]
    simp
  have choosePre (y : F) : ∃ z, j z = u y := by
    obtain ⟨⟨⟨a,d⟩, heq⟩, rfl⟩ := hk.surjective y
    exact ⟨W.mkQ d, heq.symm⟩
  choose g hg using choosePre
  let v : F →ₗ[ℂ] (X k ⧸ W) :=
    { toFun := g
      map_add' := fun x y => hj (by rw [map_add, hg, hg, hg, map_add])
      map_smul' := fun c x => hj (by simp only [map_smul, hg, RingHom.id_apply]) }
  have hv : Continuous v := by
    apply hk.isQuotientMap.continuous_iff.mpr
    convert W.continuous_mkQ.comp (continuous_snd.comp continuous_subtype_val) using 1
    funext z
    exact hj ((hg z.val.1).trans z.property)
  exact ⟨k, ⟨v, hv⟩, hg⟩

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› = sInf {t | IsLocallyConvexTopology E t ∧
      ∀ n, @Continuous (X n) E _ t Subtype.val}) (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (Y : ℕ → Submodule ℂ (E ⧸ V)) (hYmono : Monotone Y)
    (hYexh : ∀ y : E ⧸ V, ∃ n, y ∈ Y n) (hY : ∀ n, IsFrechet (Y n) ∧ IsNuclear (Y n))
    (hYtop : (inferInstance : TopologicalSpace (E ⧸ V)) = sInf {t | IsLocallyConvexTopology (E ⧸ V) t ∧
      ∀ n, @Continuous (Y n) (E ⧸ V) _ t Subtype.val}) (n : ℕ) :
    ∃ (k : ℕ) (v : Y n →L[ℂ] (X k ⧸ V.comap (X k).subtype)),
      ∀ y : Y n, Submodule.mapQ (V.comap (X k).subtype) V (X k).subtype le_rfl (v y) = (y : E ⧸ V) := by
  haveI := (bounded_in_strict_frechet_stages _ Y hYmono hYexh (fun i => (hY i).1) hYtop).1.2
  exact stage_factor X hexh (fun i => (hX i).1) V (hY n).1 (Y n).subtypeL
