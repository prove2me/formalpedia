-- Prove2me | solution 1 for GlobalTheory.CuspGL.CyclicMass.card_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:20:55.816658+00:00
-- url     : https://prove2.me/submissions/4954105c-37d5-42b4-8791-9a04c157f7ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassOfCharpolyCardCyclicVectors
import Theorems.Thm_GlobalTheory_CuspGL_CyclicMass_charpoly_mulLeft_root
import Theorems.Thm_GlobalTheory_CuspGL_CyclicMass_map_mk
import Theorems.Thm_GlobalTheory_CuspGL_CyclicMass_cyclic_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
noncomputable section
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.CyclicMass
variable {F : Type} [Field F]
namespace GlobalTheory.CuspGL.CyclicMass
theorem _root_.solution {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (D : F[X]) (hD : D.Monic)
    (hV : Module.finrank F V = D.natDegree) :
    Nat.card (AdjoinRoot D ≃ₗ[F] V) =
      Nat.card (Σ g : {g : Module.End F V // LinearMap.charpoly g = D},
        {v : V // ∀ U : Submodule F V, (∀ x ∈ U, g.1 x ∈ U) → v ∈ U → U = ⊤}) := by
  haveI : FiniteDimensional F (AdjoinRoot D) := (AdjoinRoot.powerBasis' hD).finite
  have hA : Module.finrank F (AdjoinRoot D) = D.natDegree := (AdjoinRoot.powerBasis' hD).finrank
  let Φ : (AdjoinRoot D ≃ₗ[F] V) → (Σ g : {g : Module.End F V // LinearMap.charpoly g = D},
        {v : V // ∀ U : Submodule F V, (∀ x ∈ U, g.1 x ∈ U) → v ∈ U → U = ⊤}) := fun e =>
    ⟨⟨e.conj (LinearMap.mulLeft F (AdjoinRoot.root D)), by
        rw [LinearEquiv.charpoly_conj, charpoly_mulLeft_root D hD]⟩,
      ⟨e 1, fun U hU h1 => by
        have := cyclic_one D (U.comap e.toLinearMap) (fun a ha => by
          have := hU _ ha
          simpa [LinearEquiv.conj_apply] using this) h1
        rw [eq_top_iff]
        intro v _
        have h2 : e.symm v ∈ U.comap e.toLinearMap := this ▸ Submodule.mem_top
        simpa using h2⟩⟩
  have hΦ : ∀ (e : AdjoinRoot D ≃ₗ[F] V) (p : F[X]),
      e (AdjoinRoot.mk D p) = aeval (Φ e).1.1 p (Φ e).2.1 := fun e p =>
    map_mk D e.toLinearMap _ (fun a => by simp [Φ, LinearEquiv.conj_apply]) p
  refine Nat.card_congr (Equiv.ofBijective Φ ⟨?_, ?_⟩)
  · intro e e' h
    ext a
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [hΦ, hΦ, h]
  · rintro ⟨⟨g, hg⟩, ⟨v, hv⟩⟩
    have h0 : aeval g D = 0 := hg ▸ LinearMap.aeval_self_charpoly g
    let f : AdjoinRoot D →ₗ[F] V :=
      (LinearMap.applyₗ v) ∘ₗ (aeval g).toLinearMap ∘ₗ AdjoinRoot.modByMonicHom hD
    have hf : ∀ p, f (AdjoinRoot.mk D p) = aeval g p v := fun p => by
      simp [f, AdjoinRoot.modByMonicHom_mk, Polynomial.aeval_modByMonic_eq_self_of_root h0]
    have hf1 : f 1 = v := by simpa using hf 1
    have hfx : ∀ a, f (AdjoinRoot.root D * a) = g (f a) := fun a => by
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
      rw [← AdjoinRoot.mk_X, ← map_mul, hf, hf]; simp
    have hs : Function.Surjective f := by
      rw [← LinearMap.range_eq_top]
      refine hv _ ?_ ⟨1, hf1⟩
      rintro _ ⟨a, rfl⟩
      exact ⟨_, hfx a⟩
    have hi : Function.Injective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hA.trans hV.symm)).2 hs
    refine ⟨LinearEquiv.ofBijective f ⟨hi, hs⟩, ?_⟩
    have hg' : (Φ (LinearEquiv.ofBijective f ⟨hi, hs⟩)).1 = ⟨g, hg⟩ := by
      apply Subtype.ext
      ext w
      obtain ⟨a, rfl⟩ := (LinearEquiv.ofBijective f ⟨hi, hs⟩).surjective w
      simp only [Φ, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
      exact hfx a
    refine Sigma.ext hg' ?_
    refine (Subtype.heq_iff_coe_eq ?_).2 hf1
    intro w
    rw [hg']
end GlobalTheory.CuspGL.CyclicMass
