-- Prove2me | solution 1 for GlobalTheory.isRegular_map_C_append_map_linForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:48:43.087405+00:00
-- url     : https://prove2.me/submissions/d23ee425-ad8c-463a-8f86-39e3d8b189f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Theorems.Thm_GlobalTheory_isRegular_map_C_append_map_X
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
section
open MvPolynomial RingTheory.Sequence
noncomputable section
namespace GlobalTheory
section Variables
variable {R : Type*} [CommRing R] {σ : Type*}
end Variables
section LinearForms
variable {R : Type*} [CommRing R] {ι J : Type*} [Fintype J]
variable (u : J → R) {j₀ : J} (hu : IsUnit (u j₀))
include hu
private theorem forall₂_linFormEquiv (rs : List R) (l : List ι) :
    List.Forall₂ (fun (r s : MvPolynomial (ι × J) R) => ∀ x : MvPolynomial (ι × J) R,
      (linFormEquiv u Set.univ j₀ hu).toAddEquiv (r • x) =
        s • (linFormEquiv u Set.univ j₀ hu).toAddEquiv x)
      (rs.map C ++ (l.map fun i => (i, j₀)).map X) (rs.map C ++ l.map (linForm u)) := by
  have h : (rs.map C ++ l.map (linForm u) : List (MvPolynomial (ι × J) R)) =
      (rs.map C ++ (l.map fun i => (i, j₀)).map X).map (linFormEquiv u Set.univ j₀ hu) := by
    simp only [List.map_append, List.map_map]
    congr 1
    · exact List.map_congr_left fun r _ => (linFormEquiv_C u hu _ r).symm
    · exact List.map_congr_left fun i _ => (linFormEquiv_X_of_mem u hu (Set.mem_univ i)).symm
  rw [h, List.forall₂_map_right_iff, List.forall₂_same]
  intro r _ x
  exact map_mul (linFormEquiv u Set.univ j₀ hu) r x
end LinearForms
end GlobalTheory
end
end

set_option autoImplicit false
open MvPolynomial RingTheory.Sequence
noncomputable section
open GlobalTheory
variable {R : Type*} [CommRing R] {ι J : Type*} [Fintype J]
variable (u : J → R) {j₀ : J} (hu : IsUnit (u j₀))
include hu
namespace GlobalTheory
theorem _root_.solution {rs : List R}
    (hrs : RingTheory.Sequence.IsRegular R rs) {l : List ι} (hl : l.Nodup) :
    RingTheory.Sequence.IsRegular (MvPolynomial (ι × J) R)
      (rs.map (C : R →+* MvPolynomial (ι × J) R) ++ l.map (linForm u)) :=
  (AddEquiv.isRegular_congr (forall₂_linFormEquiv u hu rs l)).1
    (isRegular_map_C_append_map_X hrs (hl.map fun _ _ h => (Prod.ext_iff.1 h).1))
end GlobalTheory
