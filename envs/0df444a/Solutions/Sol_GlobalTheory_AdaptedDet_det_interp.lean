-- Prove2me | solution 1 for GlobalTheory.AdaptedDet.det_interp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:09:32.194731+00:00
-- url     : https://prove2.me/submissions/964b516d-2f90-427b-8ca4-1ce30dd57fdc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralDetSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmUnitPowFourIdempotentModEight
import Theorems.Thm_GlobalTheory_AdaptedDet_prod_interp
import Theorems.Thm_GlobalTheory_AdaptedDet_det_smul_add
import Theorems.Thm_GlobalTheory_CongruenceDet_isIntegral_root


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AdaptedDet
namespace GlobalTheory.AdaptedDet
theorem _root_.solution {E : Type} [Field E] [NumberField E] {r : ℕ} (n : ℕ) (hn : n ≠ 0) (e t : 𝓞 E)
    (he0 : e ≠ 0) (he : e * e - e = n * t)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (g : Matrix (Fin r) (Fin r) E) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hg : ∀ v ∈ Λ, g *ᵥ v ∈ Λ) (hdet : g.det = 1) :
    ∃ y : 𝓞 E, ((e : E) • g + (1 - (e : E)) • (1 : Matrix (Fin r) (Fin r) E)).det =
      ((1 + n * y : 𝓞 E) : E) := by
  classical
  let K := AlgebraicClosure E
  have hinj := (algebraMap E K).injective
  have hn' : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hint : ∀ x : 𝓞 E, IsIntegral ℤ (algebraMap E K (x : E)) := fun x =>
    x.isIntegral_coe.algebraMap
  have hroots : ∀ μ ∈ (g.map (algebraMap E K)).charpoly.roots, IsIntegral ℤ μ := by
    intro μ hμ
    have := CongruenceDet.isIntegral_root (R := 𝓞 E) (M := 1) one_ne_zero Λ g hfg hspan
      (fun v hv => ⟨g *ᵥ v - v, sub_mem (hg v hv) hv, by simp⟩) μ
      (Polynomial.isRoot_of_mem_roots hμ)
    have h2 : IsIntegral ℤ ((μ - 1) / ((1 : ℕ) : K)) := isIntegral_trans (A := 𝓞 E) _ this
    simpa using h2.add isIntegral_one
  obtain ⟨y, hy, h⟩ := prod_interp (n : K) (algebraMap E K e) (algebraMap E K t)
    (by
      have := congrArg (fun x : 𝓞 E => algebraMap E K (x : E)) he
      simpa using this) (hint e) (hint t) _ hroots
  rw [← det_smul_add _ _ _ (by simpa using he0), ← Matrix.det_eq_prod_roots_charpoly,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one] at h
  set d := ((e : E) • g + (1 - (e : E)) • (1 : Matrix (Fin r) (Fin r) E)).det with hd
  have hd' : algebraMap E K d = 1 + n * y := by
    rw [hd, RingHom.map_det]
    have : (algebraMap E K).mapMatrix ((e : E) • g + (1 - (e : E)) • (1 : Matrix (Fin r) (Fin r) E))
        = algebraMap E K e • (algebraMap E K).mapMatrix g + (1 - algebraMap E K e) • 1 := by
      generalize (e : E) = x
      ext i j
      by_cases h : i = j <;> simp [h, -algebraMap_smul]
    rw [this, h]
    ring
  have hy' : IsIntegral ℤ ((d - 1) / n) := by
    rw [← isIntegral_algebraMap_iff hinj, map_div₀, map_sub, map_one, map_natCast, hd',
      add_sub_cancel_left, mul_div_cancel_left₀ _ hn']
    exact hy
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, (z : E) = (d - 1) / n := ⟨⟨_, hy'⟩, rfl⟩
  refine ⟨z, ?_⟩
  have hn'' : (n : E) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h1 : ((1 + n * z : 𝓞 E) : E) = 1 + n * (z : E) := by simp
  rw [h1, hz]
  field_simp
  ring
end GlobalTheory.AdaptedDet
