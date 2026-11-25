-- Prove2me | solution 1 for GlobalTheory.Reg.Enlarge.catches_enlarge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:35:00.814471+00:00
-- url     : https://prove2.me/submissions/312bc752-aa3b-4275-8f5e-38a89039cf74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralFlagChartEnlargeContainingValue
import Theorems.Thm_GlobalTheory_Reg_Enlarge_mem_of_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.Enlarge
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain Polynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
variable {O : Type} [CommRing O] {β : O →+* c.F}
attribute [local instance] Classical.propDecidable
namespace GlobalTheory.Reg.Enlarge
theorem _root_.solution (P : PChart Xo c β) (s : P.Ω) (hs : ∀ e ∈ P.es, s ∈ P.R e) {L : Type} [Field L]
    [Algebra c.F L] (W : ValuationSubring L) (hW : ∀ a : O, algebraMap c.F L (β a) ∈ W) (q : Polynomial P.Ω)
    (hqm : q.Monic) (hq0 : q.eval s = 0) (hqc : ∀ i, q.coeff i ∈ P.B) (y : FrPt Xo c L) (hy : P.Catches W y) :
    (enlarge P s hs).Catches W y := by
  obtain ⟨e, he, ψ, z, t, hg, hm, hb⟩ := hy
  have hR := eqR P s hs e he
  refine ⟨e, he, ψ.comp (Subalgebra.equivOfEq _ _ hR.symm).toAlgHom, z, t, ?_, ?_, hb⟩
  · intro g hgm
    rcases Finset.mem_insert.mp hgm with h | h
    · have hBA : ∀ x ∈ P.B, x ∈ P.R e := by
        intro x hx
        refine (Subring.closure_le (t := (P.R e).toSubring)).mpr ?_ hx
        rintro x (⟨a, rfl⟩ | hx)
        · exact Subalgebra.algebraMap_mem _ _
        · exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)
      have hWB : ∀ x (hx : x ∈ P.B), ψ ⟨x, hBA x hx⟩ ∈ W := by
        intro x hx
        have hle : P.B ≤ ((W.toSubring.comap (ψ : P.R e →+* L)).map ((P.R e).val : P.R e →+* P.Ω)) := by
          rw [Subring.closure_le]
          rintro x (⟨a, rfl⟩ | hx)
          · refine ⟨algebraMap c.F (P.R e) (β a), ?_, rfl⟩
            show ψ (algebraMap c.F (P.R e) (β a)) ∈ W
            rw [AlgHom.commutes]; exact hW a
          · exact ⟨⟨x, Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)⟩, hg _ hx, rfl⟩
        obtain ⟨a, ha, hax⟩ := hle hx
        have : a = ⟨x, hBA x hx⟩ := Subtype.ext hax
        subst this
        exact ha
      have hgR : (show P.Ω from g.1) ∈ P.R e := by rw [hR]; exact g.2
      exact mem_of_root (P.R e) P.B hBA ψ W hWB q hqm hqc (show P.Ω from g.1) hgR (by rw [h]; exact hq0)
    · exact hg (Subalgebra.equivOfEq _ _ hR.symm g) h
  · have : (ψ.comp (Subalgebra.equivOfEq _ _ hR.symm).toAlgHom).comp (Subalgebra.equivOfEq _ _ hR).toAlgHom = ψ :=
      AlgHom.ext fun _ => rfl
    exact (frMap_trPt hR (ψ.comp (Subalgebra.equivOfEq _ _ hR.symm).toAlgHom) (P.y e he) z).mpr
      (by rw [this]; exact hm)
end GlobalTheory.Reg.Enlarge
