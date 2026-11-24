-- Prove2me | solution 1 for GlobalTheory.exists_finite_complex_quasiIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:02:13.896609+00:00
-- url     : https://prove2.me/submissions/c96c7116-0363-4773-9074-6b0a8a011f50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Theorems.Thm_GlobalTheory_exists_free_complex
import Theorems.Thm_GlobalTheory_quasiIso_iff_coneExact
import Theorems.Thm_GlobalTheory_finite_ker_quotient_of_finite_homology

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory
open Limits
variable {R : Type u} [CommRing R]
namespace GlobalTheory
theorem _root_.solution [IsNoetherianRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) (hn : ∀ p, n < p → IsZero (C.X p))
    (hfin : ∀ p, Module.Finite R (C.homology p)) :
    ∃ (K : CochainComplex (ModuleCat.{u} R) ℕ) (φ : K ⟶ C),
      (∀ p, n < p → IsZero (K.X p)) ∧ (∀ p, Module.Finite R (K.X p)) ∧
      (∀ p, 1 ≤ p → Module.Free R (K.X p)) ∧ QuasiIso φ := by
  obtain ⟨m, δ, ψ, hm, hδ, hψ, h0, h1⟩ := exists_free_complex (n + 1) C.X
    (fun p => (C.d p (p + 1)).hom) (LinearMap.range (C.d 0 0).hom)
    (fun p hp => ModuleCat.isZero_iff_subsingleton.1 (hn p hp))
    (finite_ker_quotient_of_finite_homology C 0 0 1 (by simp) (by simp))
    (fun p => finite_ker_quotient_of_finite_homology C p (p + 1) (p + 2) (by simp) (by simp))
  have hC : ∀ x, (C.d 0 0).hom x = 0 := fun x => by rw [C.shape 0 0 (by simp)]; rfl
  let N := LinearMap.range ((ψ 0).prod (δ 0))
  let X : ℕ → ModuleCat.{u} R := fun p => match p with
    | 0 => ModuleCat.of R N
    | p + 1 => ModuleCat.of R (Fin (m (p + 1)) → R)
  let d : ∀ p, X p ⟶ X (p + 1) := fun p => match p with
    | 0 => ModuleCat.ofHom (LinearMap.snd R _ _ ∘ₗ N.subtype)
    | p + 1 => ModuleCat.ofHom (δ (p + 1))
  let f : ∀ p, X p ⟶ C.X p := fun p => match p with
    | 0 => ModuleCat.ofHom (LinearMap.fst R _ _ ∘ₗ N.subtype)
    | p + 1 => ModuleCat.ofHom (ψ (p + 1))
  have hd : ∀ p, d p ≫ d (p + 1) = 0 := by
    rintro (_ | p)
    · refine ModuleCat.hom_ext (LinearMap.ext ?_)
      rintro ⟨_, x, rfl⟩
      exact hδ 0 x
    · exact ModuleCat.hom_ext (LinearMap.ext (hδ (p + 1)))
  have hf : ∀ p, f p ≫ C.d p (p + 1) = d p ≫ f (p + 1) := by
    rintro (_ | p)
    · refine ModuleCat.hom_ext (LinearMap.ext ?_)
      rintro ⟨_, x, rfl⟩
      exact hψ 0 x
    · exact ModuleCat.hom_ext (LinearMap.ext (hψ (p + 1)))
  let K : CochainComplex (ModuleCat.{u} R) ℕ := CochainComplex.of X d hd
  have hKd : ∀ p, K.d p (p + 1) = d p := fun p => by simp [K, CochainComplex.of_d]
  let φ : K ⟶ C :=
    { f := f
      comm' := by
        rintro i _ rfl
        rw [hKd]
        exact hf i }
  refine ⟨K, φ, ?_, ?_, ?_, ?_⟩
  · rintro (_ | p) hp
    · omega
    · refine ModuleCat.isZero_iff_subsingleton.2 ?_
      change Subsingleton (Fin (m (p + 1)) → R)
      rw [hm _ hp]
      infer_instance
  · rintro (_ | p)
    · exact inferInstanceAs (Module.Finite R N)
    · exact inferInstanceAs (Module.Finite R (Fin (m (p + 1)) → R))
  · rintro (_ | p) hp
    · omega
    · exact inferInstanceAs (Module.Free R (Fin (m (p + 1)) → R))
  · rw [quasiIso_iff_coneExact]
    simp only [hKd]
    refine ⟨fun x hx hx' => Subtype.ext (Prod.ext hx hx'), fun c k h h' => ?_, h1⟩
    obtain ⟨x, ⟨y, hy⟩, hx⟩ := h0 c k h h'
    rw [hC] at hy
    exact ⟨⟨_, x, rfl⟩, (sub_eq_zero.1 hy.symm).symm, hx⟩
end GlobalTheory
