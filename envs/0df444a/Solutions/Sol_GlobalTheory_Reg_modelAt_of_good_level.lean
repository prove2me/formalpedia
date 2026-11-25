-- Prove2me | solution 1 for GlobalTheory.Reg.modelAt_of_good_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:23:24.752716+00:00
-- url     : https://prove2.me/submissions/f15107dd-6b65-4c5d-9d1a-6bbf7f71a90e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsValuationSubringComapEqNonunits
import Theorems.Thm_GlobalTheory_Reg_exists_valuationSubring_comap_eq_nonunits
import Theorems.Thm_GlobalTheory_Reg_exists_prime_natCast_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open GlobalTheory GlobalTheory.Reg
namespace GlobalTheory.Reg
theorem _root_.solution : PartI → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (Xo : ∀ l : Level H, Moduli Dw l) (l : Level H) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)), (∀ p : ℕ, p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p) → ModelAt (Xo l) c la := by
  intro hI E _ _ _ H Dw hpq Xo l c la hgood
  obtain ⟨-, hI⟩ := hI
  obtain ⟨Y, hY, -⟩ := hI E H Dw hpq Xo
  unfold ModelAt
  obtain ⟨p, hp, hpla⟩ := exists_prime_natCast_mem la
  obtain ⟨W, hcomap, hnon⟩ :=
    exists_valuationSubring_comap_eq_nonunits c.F.val.toRingHom (la.valuation c.F).valuationSubring
  have hlt : la.valuation c.F (p : c.F) < 1 := by
    have h := (la.valuation_lt_one_iff_mem (K := c.F) (p : 𝓞 c.F)).mpr hpla
    exact_mod_cast h
  have hp0 : (p : c.F) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpU : (p : c.F) ∈ (la.valuation c.F).valuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or]
    right
    intro hinv
    rw [Valuation.mem_valuationSubring_iff, map_inv₀] at hinv
    have hpos : 0 < la.valuation c.F (p : c.F) :=
      zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hp0)
    exact absurd ((inv_le_one₀ hpos).mp hinv) (not_le.mpr hlt)
  have hW : (p : ℂ) ∈ W.nonunits := by
    have h := hnon _ hpU
    rwa [map_natCast] at h
  let i : Idx H p := ⟨l, c, hgood p hp hpla⟩
  rw [← hcomap]
  exact ⟨Y p W hp hW i, ((hY p W hp hW).1.1 i).2.2.1⟩
end GlobalTheory.Reg
