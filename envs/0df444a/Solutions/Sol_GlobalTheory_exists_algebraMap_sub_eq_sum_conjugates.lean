-- Prove2me | solution 1 for GlobalTheory.exists_algebraMap_sub_eq_sum_conjugates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:26:07.94573+00:00
-- url     : https://prove2.me/submissions/1dcbc085-dc9e-4bf5-9003-a7a9f3af7822

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAlgebraMapSubEqSumConjugates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (y : Ω), ∃ (e : E) (s : Finset Ω), (∀ x ∈ s, x ≠ y ∧ ∃ σ : G E Ω, σ y = x) ∧ algebraMap E Ω e - y = ∑ x ∈ s, x := by
  intro E Ω _ _ _ _ _ y
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : Normal E Ω := IsAlgClosure.normal E Ω
  have hy : IsIntegral E y := Algebra.IsIntegral.isIntegral y
  set p := minpoly E y with hp
  set q := p.map (algebraMap E Ω) with hq
  have hirr : Irreducible p := minpoly.irreducible hy
  have hmon : p.Monic := minpoly.monic hy
  have hsep : q.Separable := Polynomial.Separable.map (Algebra.IsSeparable.isSeparable E y : p.Separable)
  have hnd : q.roots.Nodup := nodup_roots hsep
  have hspl : q.Splits := IsAlgClosed.splits q
  have hsum : q.nextCoeff = -q.roots.sum := hspl.nextCoeff_eq_neg_sum_roots_of_monic (hmon.map _)
  have hq0 : q ≠ 0 := (hmon.map _).ne_zero
  have hyr : y ∈ q.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hq0, IsRoot, eval_map_algebraMap]
    exact minpoly.aeval E y
  refine ⟨-p.nextCoeff, q.roots.toFinset.erase y, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxy, hxr⟩ := Finset.mem_erase.mp hx
    refine ⟨hxy, ?_⟩
    have hax : aeval x p = 0 := by
      rw [Multiset.mem_toFinset, mem_roots hq0, IsRoot, eval_map_algebraMap] at hxr
      exact hxr
    have hmx : p = minpoly E x := minpoly.eq_of_irreducible_of_monic hirr hax hmon
    have horb : x ∈ MulAction.orbit (G E Ω) y :=
      (Normal.minpoly_eq_iff_mem_orbit (F := E) Ω).mp (by rw [← hmx])
    obtain ⟨σ, hσ⟩ := horb
    exact ⟨σ, hσ⟩
  · rw [Finset.sum_erase_eq_sub hyr, Finset.sum_eq_multiset_sum, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr hnd, Multiset.map_id', map_neg, ← nextCoeff_map_eq, ← hq, hsum, neg_neg]
end GlobalTheory
