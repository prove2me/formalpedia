-- Prove2me | solution 1 for GlobalTheory.SecLimit.IsBas.reduce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:10:19.548025+00:00
-- url     : https://prove2.me/submissions/14e1be01-ab5c-4057-922c-f4b64eaf2716

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
import Theorems.Thm_GlobalTheory_SecLimit_comb_vecMul
import Theorems.Thm_GlobalTheory_SecLimit_comb_single
import Theorems.Thm_GlobalTheory_UU_CubWeil_unique


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
namespace IsBas
theorem _root_.solution {c : R →+* W} {c' : R' →+* W'} {c'' : R'' →+* W''} {ρ : W →+* W'} {ρ' : W' →+* W''}
    {g : R →+* R'} {g' : R' →+* R''} [IsLocalHom g'] (h : ∀ a, ρ (c a) = c' (g a)) (h' : ∀ a, ρ' (c' a) = c'' (g' a))
    {S : Set W} {S' : Set W'} {S'' : Set W''} (hS : ∀ s ∈ S, ρ s ∈ S') (hS' : ∀ s ∈ S', ρ' s ∈ S'')
    (hl : ∀ s ∈ S'', ∃ t ∈ S, s = ρ' (ρ t)) {b : Fin m → W} {b' : Fin m → W'} {b'' : Fin m → W''}
    (hb : IsBas c S b) (hb' : IsBas c' S' b') (hb'' : IsBas c'' S'' b'') : IsBas c' S' (fun i => ρ (b i)) := by
  choose a ha _ using fun i => hb'.2 _ (hS _ (hb.1 i))
  choose e he _ using fun i => hb''.2 _ (hS' _ (hb'.1 i))
  choose t ht ht' using fun i => hl _ (hb''.1 i)
  choose d hd _ using fun i => hb.2 _ (ht i)
  let A : Matrix (Fin m) (Fin m) R' := Matrix.of a
  let E : Matrix (Fin m) (Fin m) R'' := Matrix.of e
  let D : Matrix (Fin m) (Fin m) R'' := Matrix.of fun l i => g' (g (d l i))
  have h₁ : D * (A.map g' * E) = 1 := by
    ext l j
    have e₁ : b'' l = comb c'' b'' (Matrix.vecMul (D l) (A.map g' * E)) := by
      rw [← Matrix.vecMul_vecMul, ← comb_vecMul (a := E) he, ← comb_vecMul (v := fun i => ρ' (ρ (b i)))
        (a := A.map g') fun i => by rw [ha i, map_comb h']; rfl]
      rw [ht' l, hd l, map_comb h, map_comb h']; rfl
    have := congrFun ((hb''.2 _ (hb''.1 l)).unique e₁ (comb_single c'' b'' l)) j
    rw [Matrix.one_apply, ← Matrix.mul_apply_eq_vecMul] at *
    rw [this, Pi.single_apply]
    simp only [eq_comm]
  have hA : IsUnit A.det := by
    have := congrArg Matrix.det h₁
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one, mul_left_comm] at this
    have h₂ : IsUnit (A.map g').det := IsUnit.of_mul_eq_one _ this
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h₂
    exact IsUnit.of_map g' _ h₂
  refine ⟨fun i => hS _ (hb.1 i), fun s hs => ?_⟩
  obtain ⟨y, hy, hy'⟩ := hb'.2 s hs
  refine ⟨Matrix.vecMul y A⁻¹, ?_, fun z hz => ?_⟩
  · beta_reduce
    rw [comb_vecMul (a := A) ha, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one]
    exact hy
  · beta_reduce at hz
    rw [comb_vecMul (a := A) ha] at hz
    rw [← hy' _ hz, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hA, Matrix.vecMul_one]
end IsBas
end GlobalTheory.SecLimit
