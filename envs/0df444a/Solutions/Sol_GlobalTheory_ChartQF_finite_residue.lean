-- Prove2me | solution 1 for GlobalTheory.ChartQF.finite_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:27:38.016515+00:00
-- url     : https://prove2.me/submissions/7b253324-fcb0-4c33-825e-686c4436d2b9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAlgebraicOfMemClosure
import Theorems.Thm_GlobalTheory_ChartQF_isAlgebraic_of_mem_closure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ChartQF
variable {A R : Type} [CommRing A] [CommRing R] [IsLocalRing A] [IsLocalRing R] (f : A →+* R)
namespace GlobalTheory.ChartQF
theorem _root_.solution [IsLocalHom f] {K : Type} [Field K] [Algebra (ResidueField A) K] (ev : R →+* K)
    (hk : RingHom.ker ev = maximalIdeal R)
    (hev : ∀ a, ev (f a) = algebraMap (ResidueField A) K (residue A a)) {T : Set R} {G : Finset R}
    (hT : T ⊆ Set.range f)
    (hb : ∀ r : R, ∃ a ∈ Subring.closure (T ∪ (G : Set R)), ∃ b ∈ Subring.closure (T ∪ (G : Set R)),
      b ∉ maximalIdeal R ∧ b * r - a ∈ maximalIdeal R)
    (hG : ∀ g ∈ G, IsAlgebraic (ResidueField A) (ev g)) : ((residue R).comp f).Finite := by
  classical
  have hker : ∀ r ∈ maximalIdeal R, ev r = 0 := fun r hr => by
    rw [← RingHom.mem_ker, hk]; exact hr

  let ι : ResidueField R →+* K := Ideal.Quotient.lift (maximalIdeal R) ev hker
  have hι : ∀ r, ι (residue R r) = ev r := fun r => rfl

  let D : Subalgebra (ResidueField A) K := Algebra.adjoin (ResidueField A) ((ev : R → K) '' (G : Set R))
  have hDfin : Module.Finite (ResidueField A) D :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (G.finite_toSet.image _)
      (by rintro _ ⟨g, hg, rfl⟩; exact (hG g hg).isIntegral)
  have hB : ∀ c ∈ Subring.closure (T ∪ (G : Set R)), ev c ∈ D := fun c hc =>
    isAlgebraic_of_mem_closure f ev hev hT (D := D)
      (fun g hg => Algebra.subset_adjoin (Set.mem_image_of_mem _ hg)) hc
  have hDint : ∀ d ∈ D, IsIntegral (ResidueField A) d := fun d hd =>
    (Algebra.IsIntegral.isIntegral (R := ResidueField A) (⟨d, hd⟩ : ↥D)).map D.val

  have hrange : ∀ x : ResidueField R, ι x ∈ D := by
    intro x
    obtain ⟨r, rfl⟩ := residue_surjective x
    obtain ⟨a, ha, c, hc, hcm, hca⟩ := hb r
    have h1 : ev c * ev r = ev a := by
      have := hker _ hca
      rw [map_sub, map_mul, sub_eq_zero] at this
      exact this
    have hc0 : ev c ≠ 0 := fun h0 => hcm (by rw [← hk]; exact RingHom.mem_ker.mpr h0)
    have h2 : ev r = ev a * (ev c)⁻¹ := by rw [← h1]; field_simp
    rw [hι, h2]
    exact D.mul_mem (hB a ha) ((hDint _ (hB c hc)).inv_mem (hB c hc))
  letI : Algebra (ResidueField A) (ResidueField R) := (ResidueField.map f).toAlgebra
  have hcompat : ∀ y : ResidueField A, ι (algebraMap _ _ y) = algebraMap (ResidueField A) K y := by
    intro y
    obtain ⟨a, rfl⟩ := residue_surjective y
    show ι (ResidueField.map f (residue A a)) = _
    rw [ResidueField.map_residue, hι, hev]
  let L : ResidueField R →ₗ[ResidueField A] D :=
    { toFun := fun x => ⟨ι x, hrange x⟩
      map_add' := fun x y => Subtype.ext (map_add ι x y)
      map_smul' := fun y x => Subtype.ext (by
        simp only [Algebra.smul_def, map_mul, hcompat, RingHom.id_apply]
        rfl) }
  have hfin : Module.Finite (ResidueField A) (ResidueField R) :=
    FiniteDimensional.of_injective L (fun x y h => ι.injective (congrArg Subtype.val h))
  rw [← ResidueField.map_comp_residue f]
  exact RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ residue_surjective)
end GlobalTheory.ChartQF
