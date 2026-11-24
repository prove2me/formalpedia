-- Prove2me | solution 1 for GlobalTheory.PrimeSection.eq_zero_of_forall_pow_dvd_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:27:21.831836+00:00
-- url     : https://prove2.me/submissions/e77fc31b-576b-467e-a9c2-298915f87400

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Theorems.Thm_GlobalTheory_PrimeSection_eq_zero_of_component_eq_zero
import Theorems.Thm_GlobalTheory_PrimeElement_eq_zero_of_forall_pow_dvd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
variable {X : Scheme.{u}} [IsIntegral X]
namespace GlobalTheory.PrimeSection
theorem _root_.solution [IsLocallyNoetherian X] {t : Γ(X, ⊤)}
    {ι : Type v} {U : ι → X.Opens} (g : ∀ a b, Γ(X, U a ⊓ U b)) (s : ∀ a, Γ(X, U a))
    (hs : ∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
      g a b * X.presheaf.map (homOfLE inf_le_right).op (s b))
    {a : ι} {x : X} (hx : x ∈ U a) (hxt : x ∉ X.basicOpen t)
    (h : ∀ e : ℕ, X.presheaf.germ ⊤ x trivial t ^ e ∣ X.presheaf.germ (U a) x hx (s a))
    (b : ι) : s b = 0 := by
  have hnu : ¬ IsUnit (X.presheaf.germ ⊤ x trivial t) := fun hu => hxt ((X.mem_basicOpen_top t x).mpr hu)
  have h0 : X.presheaf.germ (U a) x hx (s a) = 0 := GlobalTheory.PrimeElement.eq_zero_of_forall_pow_dvd hnu h
  have hsa : s a = 0 := germ_injective_of_isIntegral X x hx (by rw [h0, map_zero])
  exact eq_zero_of_component_eq_zero g s hs hx hsa b
end GlobalTheory.PrimeSection
