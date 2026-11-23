-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.exists_rep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:33.892991+00:00
-- url     : https://prove2.me/submissions/095cae85-b767-4cad-a77a-45687e7a4975

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover

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
open Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ultra
variable {ι : Type} (U : Ultrafilter ι)
variable {A : ι → Type} [∀ i, CommRing (A i)] {B : Type} [CommRing B]
namespace GlobalTheory.CompanionTheory.Ultra
theorem _root_.solution [Algebra.FinitePresentation ℤ B] (g : B →+* Ult U A) :
    ∃ h : ∀ i, B → A i, Rep U h g := by
  obtain ⟨n, π, hπ, hfg⟩ := (Algebra.FinitePresentation.out : ∃ (n : ℕ)
    (f : MvPolynomial (Fin n) ℤ →ₐ[ℤ] B), Function.Surjective f ∧ (RingHom.ker f.toRingHom).FG)
  choose c hc using fun k => mk_surjective U (g (π (MvPolynomial.X k)))
  let e : ∀ i, MvPolynomial (Fin n) ℤ →+* A i := fun i =>
    MvPolynomial.eval₂Hom (Int.castRingHom _) (fun k => c k i)
  have key : (mk U).comp (Pi.ringHom e) = g.comp π.toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
    · simp
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [← hc k]
      congr 1
      ext i
      change e i (MvPolynomial.X k) = c k i
      simp [e]
  have key' : ∀ x, mk U (fun i => e i x) = g (π x) := fun x => RingHom.congr_fun key x
  obtain ⟨S, hS⟩ := hfg
  have h1 : ∀ᶠ i in (U : Filter ι), ∀ s ∈ S, e i s = 0 := by
    refine (Filter.eventually_all_finset S).2 fun s hs => ?_
    have hs' : s ∈ RingHom.ker π.toRingHom := hS ▸ Ideal.subset_span hs
    have := key' s
    rw [show π s = 0 from hs', map_zero, mk_eq_zero_iff] at this
    exact this
  refine ⟨fun i b => e i (Function.surjInv hπ b), ?_, ?_⟩
  · filter_upwards [h1] with i hi
    have hk : RingHom.ker π.toRingHom ≤ RingHom.ker (e i) := by
      rw [← hS, Ideal.span_le]
      exact fun s hs => hi s hs
    let p : B →+* A i := (RingHom.liftOfRightInverse π.toRingHom _
      (Function.rightInverse_surjInv hπ)) ⟨e i, hk⟩
    refine ⟨p, ?_⟩
    funext b
    have : p (π.toRingHom (Function.surjInv hπ b)) = e i (Function.surjInv hπ b) :=
      RingHom.liftOfRightInverse_comp_apply _ _ _ _ _
    rw [← this]
    simp [Function.surjInv_eq hπ]
  · intro b
    rw [key', Function.surjInv_eq hπ]
end GlobalTheory.CompanionTheory.Ultra
