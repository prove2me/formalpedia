-- Prove2me | solution 1 for MasulloGRH.frechet_stage_image_lifts_in_strict_quotient
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T22:56:36.95583+00:00
-- url     : https://prove2.me/submissions/03031b2e-80d4-4dbe-85e3-be4d74bd409d

import Theorems.Thm_MasulloGRH_frechet_countable_pullback_open_quotient
import Theorems.Thm_MasulloGRH_nuclear_frechet_quotient_lifts_bounded

open MasulloGRH Set Topology

-- Stage factorization from the proof of MasulloGRH.strictLF_quotient_stage_factorization
-- by dga471 (Prove2Me submission c6acacd9-c57f-4bc0-bf59-4f9e69705c7e).
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

theorem solution (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (hE : IsStrictLFOfNuclearFrechet E)
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E)) [T2Space (E ⧸ V)] (hF : IsFrechet F)
    (u : F →L[ℂ] (E ⧸ V)) (A : Set F) (hA : Bornology.IsVonNBounded ℂ A) :
    ∃ B : Set E, Bornology.IsVonNBounded ℂ B ∧ u '' A ⊆ V.mkQ '' B  := by
  obtain ⟨X, _, hcover, hX, _⟩ := hE
  obtain ⟨k, v, hv⟩ := stage_factor X hcover (fun i => (hX i).1) V hF u
  let W := V.comap (X k).subtype
  have hclosed : IsClosed (W : Set (X k)) := hV.preimage continuous_subtype_val
  have hlift := nuclear_frechet_quotient_lifts_bounded (X k) (hX k).1 (hX k).2 W hclosed
  obtain ⟨D, hD, hcontains⟩ := hlift (v '' A) (hA.image v)
  refine ⟨Subtype.val '' D, hD.image (X k).subtypeL, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨x, hx, he⟩ := hcontains ⟨y, hy, rfl⟩
  refine ⟨x, ⟨x,hx,rfl⟩, ?_⟩
  rw [← hv y, ← he]
  rfl
