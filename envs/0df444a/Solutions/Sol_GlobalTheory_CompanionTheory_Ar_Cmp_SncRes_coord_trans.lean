-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.coord_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:48:18.415943+00:00
-- url     : https://prove2.me/submissions/2f9ba01e-b98a-4729-8e96-1efa27ec62b9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCoverAndCone
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionTransitionPolynomial
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
open MvPolynomial ReciprocityTheory.AnForm.R
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
theorem _root_.solution (p p' : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p ∩ src P p') :
    ∃ (q : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)
      (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ),
      eval (coord P p x) q ≠ 0 ∧ ∀ y ∈ src P p ∩ src P p', eval (coord P p y) q ≠ 0 →
        ∀ l, coord P p' y l * eval (coord P p y) q = eval (coord P p y) (F l) := by
  classical
  obtain ⟨e, he⟩ : ∃ e, e = Fintype.equivFin (Σ k, ι k) := ⟨_, rfl⟩
  have hev : ∀ (y : Pts P) (q : Σ k, ι k), eval (coord P p y) (X (e q)) = affCoord p (rep y) q := by
    intro y q
    subst he
    simp [coord, renPt]
  have hev' : ∀ (y : Pts P) (q : Σ k, ι k), coord P p' y (e q) = affCoord p' (rep y) q := by
    intro y q
    subst he
    simp [coord, renPt]
  refine ⟨∏ k, X (e ⟨k, p' k⟩),
    fun l => X l * ∏ k ∈ Finset.univ.erase (e.symm l).1, X (e ⟨k, p' k⟩), ?_, ?_⟩
  · rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
    rw [hev]
    exact div_ne_zero (hx.2 k) (hx.1 k)
  · intro y hy _ l
    obtain ⟨r, rfl⟩ := e.surjective l
    have hprod := Finset.mul_prod_erase Finset.univ
      (fun k => affCoord p (rep y) ⟨k, p' k⟩) (Finset.mem_univ r.1)
    have hA : affCoord p' (rep y) r * affCoord p (rep y) ⟨r.1, p' r.1⟩ = affCoord p (rep y) r := by
      have h1 := hy.1 r.1
      have h2 := hy.2 r.1
      simp only [affCoord]
      field_simp
    simp only [map_prod, map_mul, hev, hev', Equiv.symm_apply_apply]
    rw [← hprod, ← mul_assoc, hA]
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
