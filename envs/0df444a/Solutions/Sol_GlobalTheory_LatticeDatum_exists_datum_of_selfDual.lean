-- Prove2me | solution 1 for GlobalTheory.LatticeDatum.exists_datum_of_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:29:23.132907+00:00
-- url     : https://prove2.me/submissions/c578f564-8171-4118-b778-4952b91be945

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeDatumOfSelfDualLattice
import Theorems.Thm_GlobalTheory_LatticeDatum_exists_datum_of_embedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix nonZeroDivisors TensorProduct
open GlobalTheory GlobalTheory.LatticeDatum
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.LatticeDatum
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E))
    (Λ' : Submodule (𝓞 E) (Fin r → E)) (_hξ : cc ξ = -ξ)
    (h : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧
      Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y)))
    (hfg : Λ'.FG) (hspan' : Submodule.span E (Λ' : Set (Fin r → E)) = ⊤)
    (hdual : ∀ v : Fin r → E, (∀ y ∈ Λ', ∃ n : ℤ, Algebra.trace ℚ E (ξ * herm Gm v y) = n) ↔ v ∈ Λ') :
    ∃ (D' : Datum H) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)), D'.p = D.p ∧ D'.q = D.q ∧ LinearMap.range φ' = Λ' ∧
      (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧
        Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ' x) (φ' y))) := by
  obtain ⟨hinj, hspan, hG, hdet, hEF⟩ := h
  haveI : Module.Finite (𝓞 E) Λ' := Module.Finite.iff_fg.mpr hfg
  obtain ⟨D', φ', hp, hq, hr, hi, hE⟩ := exists_datum_of_embedding H D ξ Gm φ hinj hspan hEF Λ' Λ'.subtype
    Λ'.injective_subtype (by rw [← LinearMap.coe_range, Submodule.range_subtype]; exact hspan')
    (fun v => by
      rw [Submodule.range_subtype, ← hdual]
      exact ⟨fun h y hy => h ⟨y, hy⟩, fun h y => h y y.2⟩)
  rw [Submodule.range_subtype] at hr
  exact ⟨D', φ', hp, hq, hr, hi, by rw [← LinearMap.coe_range, hr]; exact hspan', hG, hdet, hE⟩
end GlobalTheory.LatticeDatum
