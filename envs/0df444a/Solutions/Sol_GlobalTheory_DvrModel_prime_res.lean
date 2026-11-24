-- Prove2me | solution 1 for GlobalTheory.DvrModel.prime_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:24:17.791611+00:00
-- url     : https://prove2.me/submissions/7134118d-ade4-45f6-a8e4-4ff93df5b1bd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Theorems.Thm_GlobalTheory_DvrModel_mem_range_special
import Theorems.Thm_GlobalTheory_DvrModel_res_mem_nonZeroDivisors
import Theorems.Thm_GlobalTheory_PrimeSection_ker_app_eq_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.DvrModel
open PrimeSection
variable {V : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {K : Type u} [Field K] [Algebra V K] [IsFractionRing V K] {ϖ : V}
  {H : Scheme.{u}} {f : H ⟶ Spec (.of V)}
  {HK : Scheme.{u}} {j : HK ⟶ H} {fK : HK ⟶ Spec (.of K)}
  {Hs : Scheme.{u}} {i : Hs ⟶ H} {fs : Hs ⟶ Spec (.of (ResidueField V))}
local notation "cst[" f ", " R ", " c "]" =>
  ConcreteCategory.hom (Scheme.Hom.appTop f)
    (ConcreteCategory.hom (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of R))) c)
namespace GlobalTheory.DvrModel
theorem _root_.solution (hϖ : Irreducible ϖ) [Flat f] [IsIntegral Hs]
    (hs : IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V)))) {U : H.Opens}
    (hU : IsAffineOpen U) {x : H} (hx : x ∈ U) (hfx : f x = closedPoint V) :
    Prime (H.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op cst[f, V, ϖ]) := by
  obtain ⟨y, rfl⟩ := (mem_range_special hs x).2 hfx
  have : Nonempty (i ⁻¹ᵁ U) := ⟨⟨y, hx⟩⟩
  have : Nonempty U := ⟨⟨_, hx⟩⟩
  rw [← Ideal.span_singleton_prime
      (nonZeroDivisors.ne_zero (res_mem_nonZeroDivisors f hϖ.ne_zero hU)),
    ← ker_app_eq_span (β := CommRingCat.ofHom (residue V)) residue_surjective
      (ker_residue.trans hϖ.maximalIdeal_eq) hs hU]
  exact RingHom.ker_isPrime _
end GlobalTheory.DvrModel
