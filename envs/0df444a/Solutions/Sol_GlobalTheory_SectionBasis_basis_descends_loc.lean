-- Prove2me | solution 1 for GlobalTheory.SectionBasis.basis_descends_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:15:50.002712+00:00
-- url     : https://prove2.me/submissions/f97ae354-d511-43c7-9676-d0feb9a6d62e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDvdOfAlgebraic
import Theorems.Thm_GlobalTheory_SectionBasis_incl_algebraMap
import Theorems.Thm_GlobalTheory_SectionBasis_tmul_eq
import Theorems.Thm_GlobalTheory_SectionBasis_exists_lift_tensor
import Theorems.Thm_GlobalTheory_SectionBasis_exists_lift_quot
import Theorems.Thm_GlobalTheory_SectionBasis_mk_succ_eq_zero
import Theorems.Thm_GlobalTheory_SectionBasis_basis_descends

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SectionBasis
open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.GenericSection
open scoped TensorProduct
variable {K Kl K' : Type} [Field K] [Field Kl] [Field K'] [Algebra K Kl] [Algebra Kl K'] [Algebra K K']
  [IsScalarTower K Kl K'] {ι : Type} [Fintype ι] {Ω : ι → Type} [∀ Z, Field (Ω Z)] [∀ Z, Algebra K (Ω Z)]
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
namespace GlobalTheory.SectionBasis
theorem _root_.solution {D D' N m n : ℕ} (hD : D = D') (e : Fin m ≃ Fin (N + 1)) (j0 : ι → Fin (N + 1))
    (v : ∀ Z, Fin m → Ω Z) (x : ∀ Z, Fin N → Ω Z)
    (hv : ∀ Z, v Z (e.symm (j0 Z)) ≠ 0)
    (hx : ∀ Z k, x Z k = v Z (e.symm ((j0 Z).succAbove k)) / v Z (e.symm (j0 Z)))
    (hind : ∀ Z, AlgebraicIndependent K (sImg (D := D) (j0 Z) (x Z)))
    (hfin : ∀ Z, FiniteDimensional (IntermediateField.adjoin K (Set.range (sImg (D := D) (j0 Z) (x Z))))
      (OmS (Ω Z) D N))
    (t : Fin (D' + 1) × Fin m → K') (ht : AlgebraicIndependent K t)
    (s : ∀ Z, Fin (D' + 1) → K' ⊗[Kl] (Kl ⊗[K] Ω Z))
    (hs : ∀ Z i, s Z i = ∑ k, t (i, k) ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] v Z k))
    (I : ∀ Z, Ideal (Localization.Away (s Z 0)))
    (hI : ∀ Z, I Z = Ideal.span (Set.range fun i : Fin D' =>
      algebraMap _ (Localization.Away (s Z 0)) (s Z i.succ) * IsLocalization.Away.invSelf (s Z 0)))
    (a : ∀ Z, K' →+* Localization.Away (s Z 0) ⧸ I Z)
    (ha : ∀ Z y, a Z y = Ideal.Quotient.mk (I Z) (algebraMap K' (Localization.Away (s Z 0)) y))
    (θ : Fin n → ∀ Z, Ω Z) (g : ∀ Z, Ω Z) (hg : ∀ Z, g Z ≠ 0)
    (w : Fin n → ∀ Z, Localization.Away (s Z 0) ⧸ I Z)
    (hw : ∀ k Z, w k Z * Ideal.Quotient.mk (I Z) (algebraMap (K' ⊗[Kl] (Kl ⊗[K] Ω Z)) (Localization.Away (s Z 0))
        ((1 : K') ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] g Z))) =
      Ideal.Quotient.mk (I Z) (algebraMap (K' ⊗[Kl] (Kl ⊗[K] Ω Z)) (Localization.Away (s Z 0))
        ((1 : K') ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] θ k Z))))
    (hli : ∀ c : Fin n → K', (∀ Z, ∑ k, a Z (c k) * w k Z = 0) → ∀ k, c k = 0)
    (hsp : ∀ y : ∀ Z, Localization.Away (s Z 0) ⧸ I Z, ∃ c : Fin n → K', ∀ Z, y Z = ∑ k, a Z (c k) * w k Z) :
    ∑ Z, Module.finrank (IntermediateField.adjoin K (Set.range (sImg (D := D) (j0 Z) (x Z)))) (OmS (Ω Z) D N) = n ∧
    (∀ p : Fin n → MvPolynomial (TVar D N) K,
      (∀ Z, ∑ k, sHom (j0 Z) (x Z) (p k) * algebraMap (Ω Z) (OmS (Ω Z) D N) (θ k Z / g Z) = 0) → ∀ k, p k = 0) ∧
    (∀ y : ∀ Z, OmS (Ω Z) D N, ∃ q : MvPolynomial (TVar D N) K, (∀ Z, sHom (j0 Z) (x Z) q ≠ 0) ∧
      ∃ p : Fin n → MvPolynomial (TVar D N) K, ∀ Z, sHom (j0 Z) (x Z) q * y Z =
        ∑ k, sHom (j0 Z) (x Z) (p k) * algebraMap (Ω Z) (OmS (Ω Z) D N) (θ k Z / g Z)) := by
  subst hD
  let π : ∀ Z, K' ⊗[Kl] (Kl ⊗[K] Ω Z) →+* Localization.Away (s Z 0) ⧸ I Z := fun Z =>
    (Ideal.Quotient.mk (I Z)).comp (algebraMap _ _)
  let ψ : ∀ Z, Ω Z →+* Localization.Away (s Z 0) ⧸ I Z := fun Z => (π Z).comp (incl K Kl K')
  have ha' : ∀ Z y, a Z y = π Z (algebraMap K' _ y) := fun Z y => by
    rw [ha, IsScalarTower.algebraMap_apply K' (K' ⊗[Kl] (Kl ⊗[K] Ω Z)) (Localization.Away (s Z 0))]
    rfl
  have hwψ : ∀ k Z, w k Z = ψ Z (θ k Z / g Z) := by
    intro k Z
    have h1 : w k Z * ψ Z (g Z) = ψ Z (θ k Z) := hw k Z
    refine ((isUnit_iff_ne_zero.2 (hg Z)).map (ψ Z)).mul_right_cancel ?_
    rw [h1, ← map_mul, div_mul_cancel₀ _ (hg Z)]
  let ε : TVar D N ≃ Fin (D + 1) × Fin m := (Equiv.refl _).prodCongr e.symm
  have hs' : ∀ Z i, s Z i = ∑ j, algebraMap K' _ ((t ∘ ε) (i, j)) * incl K Kl K' (v Z (e.symm j)) := by
    intro Z i
    rw [hs, ← e.symm.sum_comp]
    exact Finset.sum_congr rfl fun j _ => tmul_eq _ _
  have hf : ∀ Z {R : Type} [CommRing R] (f : K' ⊗[Kl] (Kl ⊗[K] Ω Z) →+* R) (a' : K' →+* R) (ψ' : Ω Z →+* R),
      (∀ y, f (algebraMap K' _ y) = a' y) → (∀ ω, f (incl K Kl K' ω) = ψ' ω) → ∀ i,
      f (s Z i) = ∑ j, a' ((t ∘ ε) (i, j)) * ψ' (v Z (e.symm j)) := by
    intro Z R _ f a' ψ' h1 h2 i
    rw [hs', map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, h1, h2]
  refine basis_descends j0 (fun Z j => v Z (e.symm j)) x hv hx hind hfin (t ∘ ε)
    ((algebraicIndependent_equiv ε).2 ht) a ψ (fun Z c => ?_) (fun Z i => ?_) (fun Z R _ a' ψ' hc h0 h1 => ?_)
    (fun k Z => θ k Z / g Z) (fun c hc => hli c fun Z => ?_) (fun y => ?_)
  · rw [ha', ← incl_algebraMap]; rfl
  · rw [← hf Z (π Z) (a Z) (ψ Z) (fun y => (ha' Z y).symm) (fun _ => rfl)]
    exact mk_succ_eq_zero (s Z) (I Z) (hI Z) i
  · obtain ⟨f, hf1, hf2⟩ := exists_lift_tensor (Kl := Kl) a' ψ' hc
    obtain ⟨G, hG⟩ := exists_lift_quot (s Z) (I Z) (hI Z) f (by rw [hf Z f a' ψ' hf1 hf2]; exact h0)
      (fun i => by rw [hf Z f a' ψ' hf1 hf2]; exact h1 i)
    exact ⟨G, fun y => by rw [ha']; exact (hG _).trans (hf1 y), fun ω => (hG _).trans (hf2 ω)⟩
  · simp only [hwψ]; exact hc Z
  · obtain ⟨c, hc⟩ := hsp y
    exact ⟨c, fun Z => by rw [hc]; simp only [hwψ]⟩
end GlobalTheory.SectionBasis
