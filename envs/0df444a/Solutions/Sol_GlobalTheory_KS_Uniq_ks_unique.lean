-- Prove2me | solution 1 for GlobalTheory.KS.Uniq.ks_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:50:48.821307+00:00
-- url     : https://prove2.me/submissions/96958d34-9676-4225-9279-3049417f4ada

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EntireAntilinearLatticePeriodsConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDifferentiableOnVerticalVectorFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueUniformisingVectorVerticalTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FderivFnAddLattice
import Theorems.Thm_GlobalTheory_KS_Uniq_mem_dom_add_lattice
import Theorems.Thm_GlobalTheory_KS_Uniq_fderiv_fn_add_lattice
import Theorems.Thm_GlobalTheory_KS_Uniq_ptDer_sub
import Theorems.Thm_GlobalTheory_T_existsUnique_uniformising_vector_vertical_tangent
import Theorems.Thm_GlobalTheory_T_exists_differentiableOn_verticalVectorField
import Theorems.Thm_GlobalTheory_entire_antilinear_periods_const


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Uniq
namespace GlobalTheory.KS.Uniq
theorem _root_.solution : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D Θ Θ' s s', KSRel u p m D Θ s → KSRel u p m D Θ' s' → Θ = Θ' := by
  intro P₀ u Hm χ hG R _ x₀ X p m hp hpb D Θ Θ' s s' hs hs'
  obtain ⟨w, hwd, hw⟩ := GlobalTheory.T.exists_differentiableOn_verticalVectorField P₀ u Hm χ hG R x₀ X p m hp hpb P₀.g Set.univ id
    (fun z W f => s z W f - s' z W f) isOpen_univ differentiable_id
    (fun z _ => ⟨ptDer_sub (hs.der z) (hs'.der z), fun r => by
      show s z ⊤ (constFn p ⊤ r) - s' z ⊤ (constFn p ⊤ r) = 0
      rw [hs.base, hs'.base, sub_self]⟩)
    (fun W f => ((hs.hol W f).sub (hs'.hol W f)).mono fun z hz => hz.2)
  have hw' : ∀ z W f, z ∈ dom u m W → s z W f - s' z W f = fderiv ℂ (fn u m W f) z (w z) :=
    fun z W f hz => hw z (Set.mem_univ z) W f hz
  have hper : ∀ (l : u.Λ) z, w (z + l) = w z + (Θ - Θ').mulVec (star (l : Fin P₀.g → ℂ)) := by
    intro l z
    obtain ⟨v, -, huniq⟩ := GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hG R x₀ X p m hp hpb z
      (fun W f => s z W f - s' z W f) (ptDer_sub (hs.der z) (hs'.der z)) (fun r => by
        show s z ⊤ (constFn p ⊤ r) - s' z ⊤ (constFn p ⊤ r) = 0
        rw [hs.base, hs'.base, sub_self])
    have e1 := huniq (w z) (fun W f hz => hw' z W f hz)
    have e2 := huniq (w (z + l) - (Θ - Θ').mulVec (star (l : Fin P₀.g → ℂ))) (fun W f hz => by
      have a1 := hw' (z + l) W f ((mem_dom_add_lattice u m W z l).2 hz)
      have a2 := hs.per l W f z hz
      have a3 := hs'.per l W f z hz
      rw [fderiv_fn_add_lattice] at a1
      show s z W f - s' z W f = _
      rw [map_sub, Matrix.sub_mulVec, map_sub]
      linear_combination a1 - a2 + a3)
    rw [← e1] at e2
    exact sub_eq_iff_eq_add.mp e2
  have hdisc : DiscreteTopology u.Λ := u.discrete
  have hspan : Submodule.span ℝ (u.Λ : Set (Fin P₀.g → ℂ)) = ⊤ := u.full
  have hwd' : Differentiable ℂ w := differentiableOn_univ.mp hwd
  ext i j
  have key := GlobalTheory.entire_antilinear_periods_const P₀.g u.Λ hdisc hspan (fun z => w z i) ((Θ - Θ') i)
    (differentiable_pi.mp hwd' i) (fun l z => congrFun (hper l z) i)
  have hij := congrFun key.1 j
  simp only [Matrix.sub_apply, Pi.zero_apply, sub_eq_zero] at hij
  exact hij
end GlobalTheory.KS.Uniq
