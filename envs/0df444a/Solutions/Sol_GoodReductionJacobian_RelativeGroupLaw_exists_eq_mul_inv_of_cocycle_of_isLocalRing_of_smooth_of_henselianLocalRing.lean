-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_eq_mul_inv_of_cocycle_of_isLocalRing_of_smooth_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/8b1ca7e1-67ae-5190-b365-7f2566c875e4

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_solutionScheme_existsUnique
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_smooth_of_solutionScheme_of_cocycle
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_residueField_point_solutionScheme_of_cocycle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_eq_mul_inv_of_cocycle_of_isLocalRing_of_smooth_of_henselianLocalRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace PushTrivReduceAux
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem exists_chart {R : Type} [CommRing R] [IsLocalRing R]
    {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType gN]
    (e : Spec (CommRingCat.of R) ⟶ N) (he : e ≫ gN = 𝟙 _) :
    ∃ (A₀ : Type) (_ : CommRing A₀) (_ : Algebra R A₀) (_ : Algebra.FiniteType R A₀)
      (j : Spec (CommRingCat.of A₀) ⟶ N) (_ : IsOpenImmersion j),
      j ≫ gN = Spec.map (CommRingCat.ofHom (algebraMap R A₀)) ∧ Set.range e.base ⊆ Set.range j.base := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, -⟩ := N.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (e.base (IsLocalRing.closedPoint R))) isOpen_univ
  change IsAffineOpen U at hU
  let j : Spec Γ(N, U) ⟶ N := hU.fromSpec
  let φ : CommRingCat.of R ⟶ Γ(N, U) := Spec.preimage (j ≫ gN)
  letI : Algebra R Γ(N, U) := φ.hom.toAlgebra
  have hj : j ≫ gN = Spec.map (CommRingCat.ofHom (algebraMap R Γ(N, U))) := by
    rw [show CommRingCat.ofHom (algebraMap R Γ(N, U)) = φ from rfl, Spec.map_preimage]
  haveI : LocallyOfFiniteType (Spec.map φ) := by rw [Spec.map_preimage]; infer_instance
  have hft : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  haveI : Algebra.FiniteType R Γ(N, U) := hft
  refine ⟨Γ(N, U), inferInstance, inferInstance, inferInstance, j, inferInstance, hj, ?_⟩
  rintro _ ⟨y, rfl⟩
  rw [IsAffineOpen.range_fromSpec]
  have hsp : e.base y ⤳ e.base (IsLocalRing.closedPoint R) :=
    (IsLocalRing.specializes_closedPoint y).map e.base.hom.continuous
  exact hsp.mem_open U.2 hmem
end PushTrivReduceAux

set_option backward.isDefEq.respectTransparency false in

theorem solution
    {R : Type} [CommRing R] [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN) (hL : L.IsCommutative)
    [Smooth gN] [IsSeparated gN] [LocallyOfFiniteType gN] [QuasiCompact gN]
    (R' : Type) [CommRing R'] [Algebra R R'] [IsLocalRing R'] [Module.Finite R R'] [Module.Flat R R']
    (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) (hq : q = Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (g : SchemeHomOver (pullback.fst q q ≫ q) gN)
    (hg : L.mul (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ (pullback.fst q q ≫ q))
        (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.snd q q) (pullback.fst q q)) rfl g)
        (GoodReductionJacobian.schemeHomOverComp (pullback.snd (pullback.snd q q) (pullback.fst q q))
          (by rw [← Category.assoc, ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q),
                Category.assoc, ← pullback.condition (f := q) (g := q)]) g) =
      GoodReductionJacobian.schemeHomOverComp
        (pullback.lift (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ pullback.fst q q) (pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q)
          (by
            simp only [Category.assoc]
            rw [← pullback.condition (f := q) (g := q),
              ← Category.assoc (pullback.snd (pullback.snd q q) (pullback.fst q q)),
              ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q), Category.assoc,
              ← pullback.condition (f := q) (g := q)]))
        (by rw [← Category.assoc, pullback.lift_fst, Category.assoc]) g) :
    ∃ h : SchemeHomOver q gN,
      g = L.mul (pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst q q) rfl h)
        (L.inv (pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.snd q q) pullback.condition.symm h)) := by
  classical
  haveI : Module.Free R R' := Module.free_of_flat_of_isLocalRing

  have hchart := PushTrivReduceAux.exists_chart gN (L.one (𝟙 _)).1 (L.one (𝟙 _)).2
  obtain ⟨A₀, _, _, _, j, _, hj, hunit⟩ := hchart

  have hREP := GoodReductionJacobian.RelativeGroupLaw.exists_solutionScheme_existsUnique gN L R' q hq A₀ j hj g
  obtain ⟨P, gP, u, hsol, huniv⟩ := hREP
  have hsm : Smooth gP :=
    GoodReductionJacobian.RelativeGroupLaw.smooth_of_solutionScheme_of_cocycle gN L R' q hq A₀ j hj g hg P gP u hsol huniv
  have hx := GoodReductionJacobian.RelativeGroupLaw.exists_residueField_point_solutionScheme_of_cocycle
    gN L R' q hq A₀ j hj g hg hunit P gP u hsol huniv
  obtain ⟨x₀, hx₀⟩ := hx
  haveI := hsm
  have hs := AlgebraicGeometry.Smooth.exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing gP x₀ hx₀
  obtain ⟨s, hs1, -⟩ := hs

  let h : SchemeHomOver q gN :=
    GoodReductionJacobian.schemeHomOverComp (pullback.lift (𝟙 _) (q ≫ s) (by simp [hs1]) : Spec (CommRingCat.of R') ⟶ pullback q gP)
      (by rw [pullback.lift_fst_assoc, Category.id_comp]) u
  refine ⟨h, ?_⟩

  let j'' : pullback q q ⟶ pullback (pullback.fst q q ≫ q) gP :=
    pullback.lift (𝟙 _) ((pullback.fst q q ≫ q) ≫ s) (by simp [hs1])
  have hj'' : j'' ≫ (pullback.fst (pullback.fst q q ≫ q) gP ≫ pullback.fst q q ≫ q) = pullback.fst q q ≫ q := by
    simp only [j'', pullback.lift_fst_assoc, Category.id_comp]
  have h3 := congrArg (GoodReductionJacobian.schemeHomOverComp j'' hj'') hsol.2.2
  rw [L.mul_natural] at h3

  have e1 : GoodReductionJacobian.schemeHomOverComp j'' hj''
      (GoodReductionJacobian.schemeHomOverComp
        (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.fst q q) (𝟙 P) (𝟙 _) (by simp) (by simp))
        (by rw [pullback.lift_fst_assoc, Category.assoc]) u) =
      GoodReductionJacobian.schemeHomOverComp (pullback.fst q q) rfl h := by
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, h, j'', ← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp <;> try exact Category.id_comp _
  have e2 : GoodReductionJacobian.schemeHomOverComp j'' hj''
      (GoodReductionJacobian.schemeHomOverComp
        (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.snd q q) (𝟙 P) (𝟙 _)
          (by simp [pullback.condition]) (by simp))
        (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) u) =
      GoodReductionJacobian.schemeHomOverComp (pullback.snd q q) pullback.condition.symm h := by
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, h, j'', ← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp [pullback.condition] <;> try exact Category.id_comp _
  have e3 : GoodReductionJacobian.schemeHomOverComp j'' hj''
      (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) gP) rfl g) = g := by
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, j'', pullback.lift_fst_assoc, Category.id_comp]
  rw [e1, e2, e3] at h3

  letI : Group (SchemeHomOver (pullback.fst q q ≫ q) gN) := L.pointGroup _
  exact (eq_mul_inv_of_mul_eq h3.symm)

end S_GoodReductionJacobian_RelativeGroupLaw_exists_eq_mul_inv_of_cocycle_of_isLocalRing_of_smooth_of_henselianLocalRing
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_eq_mul_inv_of_cocycle_of_isLocalRing_of_smooth_of_henselianLocalRing (solution)
