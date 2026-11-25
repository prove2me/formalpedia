-- Prove2me | solution 1 for GlobalTheory.MonicRootExtension.exists_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:17:57.223114+00:00
-- url     : https://prove2.me/submissions/2851ab23-29e7-4358-8e2f-304129b5a162

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularLocalExtensionWithSimpleRoot
import Theorems.Thm_GlobalTheory_MonicRootExtension_isLocalRing
import Theorems.Thm_GlobalTheory_MonicRootExtension_maximalIdeal_eq
import Theorems.Thm_GlobalTheory_MonicRootExtension_isLocalHom
import Theorems.Thm_GlobalTheory_MonicRootExtension_isAdicComplete
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsRegularLocalRing_of_flat_of_map_maximalIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory GlobalTheory.MonicRootExtension
namespace GlobalTheory.MonicRootExtension
theorem _root_.solution : ∀ (A Ω : Type) [CommRing A] [IsRegularLocalRing A] [Field Ω]
    (u : A →+* Ω) (p : Polynomial A) (α : Ω),
    RingHom.ker u = maximalIdeal A → IsAdicComplete (maximalIdeal A) A → p.Monic →
    (p.map u).eval α = 0 → (p.map u).derivative.eval α ≠ 0 →
    ∃ (E : Type) (_ : CommRing E) (_ : IsRegularLocalRing E) (a : A →+* E) (v : E →+* Ω),
      a.Flat ∧ (maximalIdeal A).map a = maximalIdeal E ∧ IsAdicComplete (maximalIdeal E) E ∧
      RingHom.ker v = maximalIdeal E ∧ v.comp a = u ∧ α ∈ v.range := by
  intro A Ω _ _ _ u p α hker hcpl hp hroot _

  let ub : ResidueField A →+* Ω := Ideal.Quotient.lift (maximalIdeal A) u
    (fun x hx => (RingHom.mem_ker).1 (hker ▸ hx))
  have hub : ∀ x, ub (residue A x) = u x := fun x => rfl
  letI : Algebra (ResidueField A) Ω := ub.toAlgebra
  have hpu : p.map u = (p.map (residue A)).map ub := by
    rw [Polynomial.map_map]; congr 1
  have hint : IsIntegral (ResidueField A) α := by
    refine ⟨p.map (residue A), hp.map _, ?_⟩
    rw [← Polynomial.eval_map]; change eval α ((p.map (residue A)).map ub) = 0
    rw [← hpu]; exact hroot
  set m := minpoly (ResidueField A) α
  obtain ⟨q, hq⟩ := Polynomial.map_surjective _ (residue_surjective (R := A)) m
  obtain ⟨M, hMm, -, hM⟩ := lifts_and_natDegree_eq_and_monic ((mem_lifts _).2 ⟨q, hq⟩)
    (minpoly.monic hint)
  have hirr : Irreducible (M.map (residue A)) := hMm ▸ minpoly.irreducible hint
  haveI := isLocalRing M hM hirr
  haveI : Module.Finite A (AdjoinRoot M) := .of_basis (AdjoinRoot.powerBasis' hM).basis
  haveI : Module.Free A (AdjoinRoot M) := .of_basis (AdjoinRoot.powerBasis' hM).basis
  haveI : IsNoetherianRing (AdjoinRoot M) := isNoetherian_of_tower A inferInstance
  haveI := isLocalHom M hM hirr
  haveI : IsRegularLocalRing (AdjoinRoot M) :=
    GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.of_flat_of_map_maximalIdeal (maximalIdeal_eq M hM hirr)
  have hev : M.eval₂ u α = 0 := by
    have h1 : M.eval₂ u α = (M.map (residue A)).eval₂ ub α := by
      rw [Polynomial.eval₂_map]; rfl
    rw [h1, hMm]; exact minpoly.aeval (ResidueField A) α
  let v : AdjoinRoot M →+* Ω := AdjoinRoot.lift u α hev
  have hva : v.comp (algebraMap A (AdjoinRoot M)) = u := by
    ext x; simp [v, AdjoinRoot.algebraMap_eq]
  refine ⟨AdjoinRoot M, inferInstance, inferInstance, algebraMap A (AdjoinRoot M), v, ?_,
    maximalIdeal_eq M hM hirr, isAdicComplete M hM hirr, ?_, hva, ⟨AdjoinRoot.root M, by simp [v]⟩⟩
  · rw [RingHom.flat_algebraMap_iff]; infer_instance
  · apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top v)
    · rw [← maximalIdeal_eq M hM hirr, Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hva, ← RingHom.mem_ker, hker]
      exact hx
end GlobalTheory.MonicRootExtension
