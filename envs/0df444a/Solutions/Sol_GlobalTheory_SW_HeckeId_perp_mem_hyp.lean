-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.perp_mem_hyp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:27:17.58655+00:00
-- url     : https://prove2.me/submissions/34609de2-2d09-4080-ab21-192152e6c6df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_GlobalTheory_SW_HeckeId_exists_pole
import Theorems.Thm_GlobalTheory_SW_Nbr_co_co
import Theorems.Thm_GlobalTheory_SW_Nbr_int_move
import Theorems.Thm_GlobalTheory_SW_Nbr_mem_conjI
import Theorems.Thm_P2M_GlobalTheory_SW_Nbr_Int__symm_b5c59deb8a7e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeckeId
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
open Nbr
namespace GlobalTheory.SW.HeckeId
theorem _root_.solution {P : Ideal (𝓞 E)} [hP : P.IsMaximal] (hP0 : P ≠ ⊥) {Λ : Lt E n} (hS : SD Λ)
    {y : Fin n → E} (hy : y ∉ Λ) (hQ : ∀ c ∈ conjI P, c • y ∈ Λ) : perp Λ y ∈ Hyp P Λ := by
  obtain ⟨t, ht, d, hd, r, hr, e⟩ := exists_pole P hP0
  have hint : ∀ c ∈ P, ∀ x : Λ, IsIntegral ℤ ((c : E) * herm 1 (x : Fin n → E) y) := fun c hc x => by
    have h1 : co c ∈ conjI P := mem_conjI.2 (by rwa [co_co])
    have h2 := (int_move c (x : Fin n → E) y).2 ((hS _).1 x.2 _ (hQ _ h1))
    unfold Int' at h2
    rwa [osmul, herm_sl] at h2
  let g : Λ →ₗ[𝓞 E] 𝓞 E :=
    { toFun := fun x => ⟨_, hint d hd x⟩
      map_add' := fun x x' => RingOfIntegers.ext (by
        change (d : E) * herm 1 ((x : Fin n → E) + (x' : Fin n → E)) y = (d : E) * _ + (d : E) * _
        rw [herm_al, mul_add])
      map_smul' := fun c x => RingOfIntegers.ext (by
        change (d : E) * herm 1 ((c : E) • (x : Fin n → E)) y = (c : E) * ((d : E) * _)
        rw [herm_sl, mul_left_comm]) }
  have hk : LinearMap.ker (P.mkQ ∘ₗ g) = perp Λ y := by
    ext x
    refine (Submodule.Quotient.mk_eq_zero P).trans ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨u, c, hc, huc⟩ := hP.exists_inv hr
      have h3 : (u : E) * (r : E) + (c : E) = 1 := by
        exact_mod_cast congrArg (fun a : 𝓞 E => (a : E)) huc
      have h4 : IsIntegral ℤ ((d : E) * herm 1 (x : Fin n → E) y * t) := ht _ hx
      have h5 : herm 1 (x : Fin n → E) y = (u : E) * ((d : E) * herm 1 (x : Fin n → E) y * t) +
          (c : E) * herm 1 (x : Fin n → E) y := by
        linear_combination (-herm 1 (x : Fin n → E) y) * h3 + (u : E) * herm 1 (x : Fin n → E) y * e
      change IsIntegral ℤ (herm 1 (x : Fin n → E) y)
      rw [h5]
      exact (IsIntegral.mul u.2 h4).add (hint c hc x)
    · have hx : IsIntegral ℤ (herm 1 (x : Fin n → E) y) := hx
      let w : 𝓞 E := ⟨_, hx⟩
      have h1 : g x = w * d := RingOfIntegers.ext (mul_comm (d : E) (w : E))
      rw [h1]
      exact P.mul_mem_left _ hd
  refine ⟨_, fun h0 => hy ((hS y).2 fun z hz => Int'.symm ?_), hk⟩
  have : (⟨z, hz⟩ : Λ) ∈ perp Λ y := by rw [← hk, h0]; trivial
  exact this
end GlobalTheory.SW.HeckeId
