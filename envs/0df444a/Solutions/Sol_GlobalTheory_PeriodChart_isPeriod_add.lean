-- Prove2me | solution 1 for GlobalTheory.PeriodChart.isPeriod_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:39:52.547557+00:00
-- url     : https://prove2.me/submissions/fb87e07f-0da5-442c-9b32-1917ca5c06ae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
import Theorems.Thm_GlobalTheory_PeriodChart_sesq_apply
import Theorems.Thm_GlobalTheory_PeriodChart_exists_herm
import Theorems.Thm_GlobalTheory_PeriodChart_lattice_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}
variable {D : Datum H} {ty : Fin g → (E →+* ℂ)}
namespace GlobalTheory.PeriodChart
theorem _root_.solution (P : D.La →+ (Fin g → ℂ)) (hl : ∀ (a : 𝓞 E) x, P (a • x) = dg ty a *ᵥ P x)
    (hi : Function.Injective P) (hd : DiscreteTopology P.range)
    (hs : Submodule.span ℝ (Set.range P) = ⊤) (G : Matrix (Fin g) (Fin g) ℂ) (hG : G.IsHermitian)
    (hE : ∀ x y, (sesq G (P x) (P y)).im = D.EF x y) (Z : Matrix (Fin g) (Fin g) ℂ)
    (h1 : ∀ a z, anti Z (dg ty a *ᵥ z) = dg ty a *ᵥ anti Z z)
    (h2 : ∀ z w, sesq G (anti Z z) w = sesq G (anti Z w) z)
    (h3 : ∀ z, z ≠ 0 → (sesq G (anti Z z) (anti Z z)).re < (sesq G z z).re) :
    IsPeriod D ty (P + (anti Z).toAddMonoidHom.comp P) := by

  let T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
    { toFun := fun z => z + anti Z z
      map_add' := fun x y => by simp only [map_add]; abel
      map_smul' := fun r x => by
        simp only [RingHom.id_apply, smul_add, ← Complex.coe_smul, LinearMap.map_smulₛₗ,
          Complex.conj_ofReal] }
  have hT : ∀ z, T z = z + anti Z z := fun z => rfl

  have hTi : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    by_contra hne
    have hN : anti Z z = -z := eq_neg_of_add_eq_zero_right (by rw [← hT]; exact hz)
    have := h3 z hne
    simp only [hN, map_neg, LinearMap.neg_apply, neg_neg] at this
    exact lt_irrefl _ this
  obtain ⟨hi', hd', hs'⟩ := lattice_map P (P + (anti Z).toAddMonoidHom.comp P) hi hd hs T hTi
    (fun a => rfl)
  obtain ⟨Hm, hH, hpos, him⟩ := exists_herm G Z hG h2 h3
  refine ⟨fun a x i => ?_, hi', hd', hs', Hm, hH, fun z hz => ?_, fun x y => ?_⟩
  · change P (a • x) i + anti Z (P (a • x)) i = ty i (a : E) * (P x i + anti Z (P x) i)
    rw [hl, h1]
    simp only [dg, Matrix.mulVec_diagonal]
    ring
  · rw [← sesq_apply]; exact hpos z hz
  · rw [← sesq_apply]
    change (sesq Hm (P x + anti Z (P x)) (P y + anti Z (P y))).im = _
    rw [him, hE]
end GlobalTheory.PeriodChart
