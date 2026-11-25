-- Prove2me | solution 1 for GlobalTheory.SS.Ord.exists_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:13:38.336781+00:00
-- url     : https://prove2.me/submissions/5ea4e6ef-9ef8-43d3-9ae6-92ad1aa32ac4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Theorems.Thm_GlobalTheory_SS_Ord_exists_prime_iInf
import Theorems.Thm_GlobalTheory_SS_Ord_j_cst
import Theorems.Thm_GlobalTheory_SS_Ord_j_app_injective
import Theorems.Thm_GlobalTheory_SS_Ord_rs_j
import Theorems.Thm_GlobalTheory_SS_Ord_rs_jac
import Theorems.Thm_GlobalTheory_SS_Ord_isOpenImmersion_j
import Theorems.Thm_GlobalTheory_SS_Ord_mem_basicOpen_cst
import Theorems.Thm_GlobalTheory_SS_Ord_mem_range_j
import Theorems.Thm_GlobalTheory_SS_Ord_j_app_surjective
import Theorems.Thm_GlobalTheory_SS_Ord_cst_mem_nonZeroDivisors
import Theorems.Thm_GlobalTheory_SS_Ord_prime_cst
import Theorems.Thm_GlobalTheory_SS_Ord_jac_mem_basicOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Ord
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] {A : Over (Sp K)} {π : R} {I : Type} [Fintype I] [DecidableEq I]
namespace GlobalTheory.SS.Ord
theorem _root_.solution (hπ : Irreducible π) (M : Model R A) (hM : M.Irr) {D : I → VF A} (hD : IsFrame D)
    {U : M.Y.left.Opens} (hU : IsAffineOpen U) (h : ((U : Set M.Y.left) ∩ M.sp).Nonempty) :
    ∃ m : ℕ, ¬ ∀ t : I → Γ(M.Y.left, U), ∃ s : Γ(M.Y.left, U),
      jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) =
        cstK A _ (algebraMap R K π ^ (m : ℤ)) * (M.j.app U).hom s := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  obtain ⟨J, hJ, hπJ, hJ'⟩ := exists_prime_iInf (prime_cst hπ M hM hU h) (cst_mem_nonZeroDivisors hπ M U)
  have h1 : ∀ t : I → Γ(M.Y.left, U), ∃ s ∈ J,
      (M.j.app U).hom s = jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) := fun t => by
    obtain ⟨s, hs⟩ := hcon 0 t
    rw [Nat.cast_zero, zpow_zero, map_one, _root_.one_mul] at hs
    refine ⟨s, hJ' s fun n => ?_, hs.symm⟩
    obtain ⟨s', hs'⟩ := hcon n t
    refine ⟨s', j_app_injective M U ?_⟩
    rw [← hs, hs', map_mul, map_pow, j_cst, zpow_natCast, map_pow]
  let p : PrimeSpectrum Γ(M.Y.left, U) := ⟨J, hJ⟩
  have hx : hU.fromSpec p ∈ M.Y.left.basicOpen (cst M U π) := (hU.fromSpec_preimage_basicOpen _).ge hπJ
  obtain ⟨hxU, hxs⟩ := (mem_basicOpen_cst hπ M U _).1 hx
  obtain ⟨y, hy⟩ := (mem_range_j M _).2 hxs
  obtain ⟨V, t, hyV, ht⟩ := hD.2 y
  have := isOpenImmersion_j M
  obtain ⟨g, hg, hxg⟩ := hU.exists_basicOpen_le (V := M.j ''ᵁ V) ⟨hU.fromSpec p, y, hyV, hy⟩ hxU
  have hgJ : g ∉ J := (hU.fromSpec_preimage_basicOpen g).le hxg
  have hle : M.j ⁻¹ᵁ M.Y.left.basicOpen g ≤ V := (M.j.preimage_mono hg).trans (M.j.preimage_image_eq V).le
  have hsurj := j_app_surjective M (U := M.Y.left.basicOpen g) fun x hx => by
    obtain ⟨z, -, rfl⟩ := hg hx
    exact (mem_range_j M _).1 ⟨z, rfl⟩
  choose t' ht' using fun i => hsurj (rs _ hle (t i))
  let J' : Ideal Γ(M.Y.left, M.Y.left.basicOpen g) := J.map (rs _ (M.Y.left.basicOpen_le g))
  have key := jac_mem_basicOpen M D hU g (J'.toAddSubgroup.map (M.j.app _).hom.toAddMonoidHom)
    (by rintro s _ ⟨x, hx, rfl⟩; exact ⟨s * x, J'.mul_mem_left s hx, map_mul (M.j.app _).hom s x⟩)
    (fun t => by
      obtain ⟨s, hs, e⟩ := h1 t
      exact ⟨_, Ideal.mem_map_of_mem _ hs, by rw [← e, rs_j M (M.Y.left.basicOpen_le g)]; rfl⟩) t'
  obtain ⟨u, hu, e⟩ := key
  have hu' : IsUnit ((M.j.app (M.Y.left.basicOpen g)).hom u) := by
    have := ht.map (rs _ hle)
    rw [rs_jac] at this
    simp only [← ht'] at this
    exact e ▸ this
  have hu'' : IsUnit u := by
    obtain ⟨v, hv⟩ := hu'.exists_right_inv
    obtain ⟨w, rfl⟩ := hsurj v
    exact IsUnit.of_mul_eq_one w (j_app_injective M _ (by rw [map_mul, hv, map_one]))
  have hl := hU.isLocalization_basicOpen g
  have hdis : Disjoint (Submonoid.powers g : Set Γ(M.Y.left, U)) J := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ hk
    exact hgJ (hJ.mem_of_pow_mem k hk)
  have hpr := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g)
    Γ(M.Y.left, M.Y.left.basicOpen g) J hJ hdis
  exact hpr.ne_top (Ideal.eq_top_of_isUnit_mem _ hu hu'')
end GlobalTheory.SS.Ord
