-- Prove2me | solution 1 for GlobalTheory.SecLimit.existsUnique_limit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:37:36.61139+00:00
-- url     : https://prove2.me/submissions/4c3998a1-6ccc-4ff4-b1d2-313e2afdcaf4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueLimit
import Theorems.Thm_GlobalTheory_SecLimit_map_comb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.SecLimit
universe u
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {W W' W'' : Type u} [CommRing W] [CommRing W']
  [CommRing W''] {m : ℕ}
namespace GlobalTheory.SecLimit
theorem _root_.solution (I : Ideal R) [IsAdicComplete I R] {T : ℕ → Type u} [∀ e, CommRing (T e)]
    {c : R →+* W} {c' : ∀ e, R ⧸ I ^ (e + 1) →+* T e} {ρ : ∀ e, W →+* T e} {τ : ∀ e, T (e + 1) →+* T e}
    (h : ∀ e a, ρ e (c a) = c' e (Ideal.Quotient.mk _ a)) (hτ : ∀ e s, τ e (ρ (e + 1) s) = ρ e s)
    {S : Set W} {S' : ∀ e, Set (T e)} {b : Fin m → W} (hS : ∀ z, comb c b z ∈ S)
    (hb : IsBas c S b) (hb' : ∀ e, IsBas (c' e) (S' e) (fun i => ρ e (b i)))
    (f : ∀ e, T e) (hf : ∀ e, f e ∈ S' e) (hc : ∀ e, τ e (f (e + 1)) = f e) : ∃! s, s ∈ S ∧ ∀ e, ρ e s = f e := by
  choose z hz hz' using fun e => (hb' e).2 _ (hf e)
  choose y hy using fun e i => Ideal.Quotient.mk_surjective (z e i)
  have key : ∀ e (x : Fin m → R), ρ e (comb c b x) = f e ↔ ∀ i, x i - y e i ∈ I ^ (e + 1) := fun e x => by
    rw [map_comb (h e)]
    simp only [← Ideal.Quotient.eq, hy]
    exact ⟨fun H => congrFun (hz' e _ H.symm), fun H => by rw [funext H]; exact (hz e).symm⟩
  have step : ∀ e i, y (e + 1) i - y e i ∈ I ^ (e + 1) := fun e => (key e _).1 (by
    rw [← hτ, (key (e + 1) _).2 fun i => by rw [sub_self]; exact zero_mem _, hc])
  have hL : ∀ i, ∃ L : R, ∀ e, L - y e i ∈ I ^ (e + 1) := fun i => by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := R) inferInstance (f := fun e => y e i)
      ((AdicCompletion.isAdicCauchy_iff I R _).2 fun n => by
        rw [smul_eq_mul, Ideal.mul_top]
        exact (SModEq.sub_mem.2 (Ideal.pow_le_pow_right n.le_succ (step n i))).symm)
    refine ⟨L, fun e => ?_⟩
    have := hL (e + 1)
    rw [smul_eq_mul, Ideal.mul_top] at this
    have := add_mem (SModEq.sub_mem.1 this.symm) (step e i)
    rwa [sub_add_sub_cancel] at this
  choose L hL using hL
  refine ⟨comb c b L, ⟨hS L, fun e => (key e L).2 fun i => hL i e⟩, fun s ⟨hs, hs'⟩ => ?_⟩
  obtain ⟨x, rfl, -⟩ := hb.2 s hs
  congr 1
  funext i
  refine sub_eq_zero.1 (IsHausdorff.haus (I := I) (M := R) inferInstance _ fun n => ?_)
  rw [smul_eq_mul, Ideal.mul_top, SModEq.zero]
  have := sub_mem ((key n x).1 (hs' n) i) (hL i n)
  rw [sub_sub_sub_cancel_right] at this
  exact Ideal.pow_le_pow_right n.le_succ this
end GlobalTheory.SecLimit
