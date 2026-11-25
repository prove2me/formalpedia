-- Prove2me | solution 1 for GlobalTheory.ChartQF.quasiFinite_of_pointRigid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:29:07.239572+00:00
-- url     : https://prove2.me/submissions/eeabbdb2-92dd-4774-9b1a-0b89d9e57fa3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAlgebraicOfMemClosure
import Theorems.Thm_GlobalTheory_ChartQF_finite_residue
import Theorems.Thm_GlobalTheory_ChartQF_exists_geomPoint
import Theorems.Thm_GlobalTheory_ChartQF_range_subset_stalk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.ChartQF
section Alg
variable {A R : Type} [CommRing A] [CommRing R] [IsLocalRing A] [IsLocalRing R] (f : A →+* R)
end Alg
private theorem nonempty_ringHom_of_algebraic_subfield {k K L : Type} [Field k] [Field K] [Field L] [IsAlgClosed L] [Algebra k K]
    (k₀ : Subfield K) (hmem : ∀ x, x ∈ k₀ ↔ IsAlgebraic k x) (ψ : k →+* L) : Nonempty (k₀ →+* L) := by
  letI : Algebra k L := ψ.toAlgebra
  let E : IntermediateField k K :=
    k₀.toIntermediateField (fun x => (hmem _).mpr (isAlgebraic_algebraMap x))
  haveI : Algebra.IsAlgebraic k E :=
    ⟨fun x => IntermediateField.isAlgebraic_iff.mpr ((hmem _).mp x.2)⟩
  exact ⟨(IsAlgClosed.lift : E →ₐ[k] L).toRingHom⟩
end GlobalTheory.ChartQF
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ChartQF
namespace GlobalTheory.ChartQF
theorem _root_.solution {F R : Type} [CommRing F] [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (ξ : Sp R ⟶ S)
    (σ : S ⟶ Sp F) (b : F →+* R) (hb : ξ ≫ σ = spMap b) (hft : ((residue R).comp b).EssFiniteType)
    (hc : ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
      Nonempty (k₀ →+* AlgebraicClosure (ResidueField R)) →
      (∀ q, (spMap ev ≫ ξ) q = ξ (closedPoint R)) → (∃ P₀ : Sp k₀ ⟶ S, spMap k₀.subtype ≫ P₀ = spMap ev ≫ ξ) →
      (∀ r ∈ maximalIdeal R, ev r = 0) ∧ ∀ r, ev r ∈ k₀) :
    (∀ p : Sp R, ξ p = ξ (closedPoint R) → p = closedPoint R) ∧
      ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).Finite := by
  classical

  have key : ∀ p : Sp R, ξ p = ξ (closedPoint R) → ∃ (K : Type) (_ : Field K)
      (_ : Algebra (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) K) (ev : R →+* K),
      RingHom.ker ev = p.asIdeal ∧
      (∀ a, ev ((Scheme.stalkClosedPointTo ξ).hom a) = algebraMap _ K (residue _ a)) ∧
      (∀ r ∈ maximalIdeal R, ev r = 0) ∧
      ∀ r, IsAlgebraic (ResidueField (S.presheaf.stalk (ξ (closedPoint R)))) (ev r) := by
    intro p hp
    obtain ⟨K, _, _, _, ev, k₀, hk₀, hker, hev, hmem, hpts, hP₀⟩ := exists_geomPoint ξ p hp
    have hemb : Nonempty (k₀ →+* AlgebraicClosure (ResidueField R)) :=
      nonempty_ringHom_of_algebraic_subfield k₀ hmem ((algebraMap (ResidueField R) (AlgebraicClosure (ResidueField R))).comp
        (ResidueField.map (Scheme.stalkClosedPointTo ξ).hom))
    obtain ⟨h1, h2⟩ := hc K ev k₀ hk₀ hemb hpts hP₀
    exact ⟨K, inferInstance, inferInstance, ev, hker, hev, h1, fun r => (hmem _).mp (h2 r)⟩
  constructor
  · intro p hp
    obtain ⟨K, _, _, ev, hker, -, h1, -⟩ := key p hp
    apply PrimeSpectrum.ext
    refine le_antisymm (le_maximalIdeal p.isPrime.ne_top) ?_
    intro r hr
    rw [← hker]
    exact h1 r hr
  · obtain ⟨K, _, _, ev, hker, hev, -, h2⟩ := key (closedPoint R) rfl

    letI : Algebra F (ResidueField R) := ((residue R).comp b).toAlgebra
    haveI : Algebra.EssFiniteType F (ResidueField R) := hft
    obtain ⟨s, hs⟩ := Algebra.EssFiniteType.cond (R := F) (S := ResidueField R)
    let lift : ResidueField R → R := fun z => (residue_surjective z).choose
    have hlift : ∀ z, residue R (lift z) = z := fun z => (residue_surjective z).choose_spec
    let G : Finset R := s.image lift
    have hadj : ∀ z ∈ Algebra.adjoin F (s : Set (ResidueField R)),
        ∃ a ∈ Subring.closure (Set.range b ∪ (G : Set R)), residue R a = z := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem x hx =>
        exact ⟨lift x, Subring.subset_closure (Or.inr (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx))),
          hlift x⟩
      | algebraMap x => exact ⟨b x, Subring.subset_closure (Or.inl ⟨x, rfl⟩), rfl⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨c, hc, rfl⟩ := hy
        exact ⟨a + c, add_mem ha hc, map_add _ _ _⟩
      | mul x y _ _ hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨c, hc, rfl⟩ := hy
        exact ⟨a * c, mul_mem ha hc, map_mul _ _ _⟩
    have hb' : ∀ r : R, ∃ a ∈ Subring.closure (Set.range b ∪ (G : Set R)),
        ∃ c ∈ Subring.closure (Set.range b ∪ (G : Set R)),
          c ∉ maximalIdeal R ∧ c * r - a ∈ maximalIdeal R := by
      intro r
      obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.mk'_surjective
        ((IsUnit.submonoid (ResidueField R)).comap
          (algebraMap (Algebra.adjoin F (s : Set (ResidueField R))) (ResidueField R)))
        (S := ResidueField R) (residue R r)
      have hspec := IsLocalization.mk'_spec (ResidueField R) x y
      simp only at hxy
      rw [hxy] at hspec
      obtain ⟨a, ha, hae⟩ := hadj x.1 x.2
      obtain ⟨c, hc, hce⟩ := hadj y.1.1 y.1.2
      have hyu : IsUnit (y.1.1 : ResidueField R) := y.2
      refine ⟨a, ha, c, hc, ?_, ?_⟩
      · rw [← residue_eq_zero_iff, hce]
        exact hyu.ne_zero
      · rw [← residue_eq_zero_iff, map_sub, map_mul, hce, hae, mul_comm, sub_eq_zero]
        exact hspec
    exact finite_residue (Scheme.stalkClosedPointTo ξ).hom ev hker hev (range_subset_stalk ξ σ b hb) hb'
      (fun g _ => h2 g)
end GlobalTheory.ChartQF
