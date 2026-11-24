-- Prove2me | solution 1 for GlobalTheory.LatBasisAt.basisAtEx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:19:54.045358+00:00
-- url     : https://prove2.me/submissions/404a5ec7-e012-4644-a780-e90a81e80278

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LatticeHasBasisAtEveryFinitePlace
import Theorems.Thm_GlobalTheory_LatBasisAt_mem_localization_iff_mem_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.LatBasisAt
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.LatBasisAt
theorem _root_.solution : Formalism.L2.DIV.BasisAtEx := by
  intro K _ _ d L hL w
  haveI := w.isPrime
  have : IsDiscreteValuationRing (locRing w) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) w.ne_bot (locRing w)
  set N : Submodule (locRing w) (Fin d → K) := Submodule.span (locRing w) (L : Set (Fin d → K))
    with hN
  have : Module.Finite (locRing w) N := by
    obtain ⟨s, hs⟩ := hL.fg
    rw [Module.Finite.iff_fg]
    refine ⟨s, ?_⟩
    rw [hN, ← hs, Submodule.span_span_of_tower]
  have : Module.IsTorsionFree (locRing w) N := inferInstance
  let b := Module.Free.chooseBasis (locRing w) N
  let v : Module.Free.ChooseBasisIndex (locRing w) N → Fin d → K := fun i => (b i : Fin d → K)
  have hliA : LinearIndependent (locRing w) v := b.linearIndependent.map' N.subtype N.ker_subtype
  have hli : LinearIndependent K v := (LinearIndependent.iff_fractionRing (locRing w) K).mp hliA
  have hspanA : Submodule.span (locRing w) (Set.range v) = N := by
    have : Set.range v = N.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspan : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← hL.span_eq_top, Submodule.span_le]
    intro x hx
    have hxN : x ∈ Submodule.span (locRing w) (Set.range v) := by
      rw [hspanA]; exact Submodule.subset_span hx
    exact Submodule.span_le_restrictScalars (locRing w) K _ hxN
  let bK : Basis _ K (Fin d → K) := Basis.mk hli hspan
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex (locRing w) N) = d := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]
  let e := Fintype.equivFinOfCardEq hcard
  have hli' : LinearIndependent K (v ∘ e.symm) := hli.comp _ e.symm.injective
  let P : Matrix (Fin d) (Fin d) K := Matrix.of fun a j => (v ∘ e.symm) j a
  have hP : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp hli'
  refine ⟨hP.unit, ?_⟩
  have hcol : Formalism.L2.DIV.colLat hP.unit = Submodule.span (𝓞 K) (Set.range (v ∘ e.symm)) := rfl
  unfold Formalism.L2.DIV.IsBasisAt
  ext x
  rw [hcol, mem_localization_iff_mem_span, mem_localization_iff_mem_span, Submodule.span_span_of_tower,
    EquivLike.range_comp, hspanA]
end GlobalTheory.LatBasisAt
