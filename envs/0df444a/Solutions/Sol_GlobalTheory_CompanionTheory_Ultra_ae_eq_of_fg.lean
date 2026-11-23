-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.ae_eq_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:33.417521+00:00
-- url     : https://prove2.me/submissions/bafa4b3d-bb8c-4b5e-b96b-e64bb3860609

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
theorem _root_.solution [Algebra.FiniteType ℤ B] {h h' : ∀ i, B → A i} (hh : IsAEHom U h)
    (hh' : IsAEHom U h') (H : ∀ b, mk U (fun i => h i b) = mk U (fun i => h' i b)) :
    ∀ᶠ i in (U : Filter ι), h i = h' i := by
  obtain ⟨S, hS⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra ℤ B).FG)
  have h1 : ∀ᶠ i in (U : Filter ι), ∀ s ∈ S, h i s = h' i s :=
    (Filter.eventually_all_finset S).2 fun s _ => (mk_eq_mk_iff U).1 (H s)
  filter_upwards [h1, hh, hh'] with i hi ⟨p, hp⟩ ⟨q, hq⟩
  have : p.toIntAlgHom = q.toIntAlgHom := by
    refine AlgHom.ext_of_adjoin_eq_top hS ?_
    intro s hs
    have := hi s hs
    rw [← hp, ← hq] at this
    exact this
  rw [← hp, ← hq]
  ext b
  exact DFunLike.congr_fun this b
end GlobalTheory.CompanionTheory.Ultra
