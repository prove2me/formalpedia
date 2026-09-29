-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_toricLift_of_torusFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/2409b4ba-fe0f-542a-a344-4ca734919104

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_AlgebraicGeometry_SplitTorus_existsUnique_muLift_baseChange_of_torusFibre_of_henselian
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_AlgebraicGeometry_SplitTorus_exists_conj_muHom_baseChange
import Theorems.Thm_AlgebraicGeometry_SplitTorus_exists_addEquiv_eq_specMap_mapDomain_comp_of_range_eq
import Theorems.Thm_AlgebraicGeometry_SplitTorus_exists_twist_torusHom_baseChange_of_ringEquiv
import Theorems.Thm_AlgebraicGeometry_eq_of_isClosed_of_forall_rationalPoint_mem_iff
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_range_subset_of_isReduced
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_inertia_smul_eq_and_exists_decomposition_smul_eq_of_muLift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_toricLift_of_torusFibre
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff"

set_option autoImplicit false

universe u

noncomputable section glue
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SplitTorus IsLocalRing

namespace TLGlue

variable {R₀ : Type u} [CommRing R₀] {A : Type u} [CommRing A] [IsLocalRing A]

theorem muIncl_comp_muStr (t : ℕ) {m m' : ℕ} (h : m ∣ m') : muIncl A t h ≫ muStr A t m' = muStr A t m := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  simp [AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.mapDomain_single]

theorem muBaseChange_comp_muIncl {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S') (t : ℕ) {m m' : ℕ} (h : m ∣ m') :
    muBaseChange φ t m ≫ muIncl S t h = muIncl S' t h ≫ muBaseChange φ t m' := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    AddMonoidAlgebra.mapRingHom_comp_mapDomainRingHom]

theorem muIncl_comp_muToTorus (S : Type u) [CommRing S] (t : ℕ) {m m' : ℕ} (h : m ∣ m') :
    muIncl S t h ≫ muToTorus S t m' = muToTorus S t m := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← AddMonoidAlgebra.mapDomainRingHom_comp]
  congr 3
  ext v i
  simp [ZMod.cast_intCast h]

def pushChar {S : Type u} [CommRing S] [Algebra A S] (t : ℕ) {m m' : ℕ} (h : m ∣ m')
    (χ : muCoord A t m →ₐ[A] S) : muCoord A t m' →ₐ[A] S :=
  χ.comp (AddMonoidAlgebra.mapDomainAlgHom A A
    (AddMonoidHom.pi fun i => ((ZMod.castHom h (ZMod m)).toAddMonoidHom).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ZMod m') i)))

theorem muPt_pushChar {S : Type u} [CommRing S] [Algebra A S] (t : ℕ) {m m' : ℕ} (h : m ∣ m')
    (χ : muCoord A t m →ₐ[A] S) : (muPt A S t m' (pushChar t h χ)).1 = (muPt A S t m χ).1 ≫ muIncl A t h := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem pushChar_mul {S : Type u} [CommRing S] [Algebra A S] (t : ℕ) {m m' : ℕ} (h : m ∣ m')
    (χ χ' : WithConv (muCoord A t m →ₐ[A] S)) :
    pushChar t h (χ * χ').ofConv = (WithConv.toConv (pushChar t h χ.ofConv) * WithConv.toConv (pushChar t h χ'.ofConv)).ofConv := by
  have key : ∀ (n : ℕ) (ψ ψ' : WithConv (muCoord A t n →ₐ[A] S)) (g : Fin t → ZMod n),
      (ψ * ψ').ofConv (AddMonoidAlgebra.single g 1) =
        ψ.ofConv (AddMonoidAlgebra.single g 1) * ψ'.ofConv (AddMonoidAlgebra.single g 1) := by
    intro n ψ ψ' g
    rw [AlgHom.convMul_def]
    simp [AddMonoidAlgebra.comul_single, Algebra.TensorProduct.lmul'_apply_tmul]
  have hmd : ∀ (ψ : muCoord A t m →ₐ[A] S) (g : Fin t → ZMod m'),
      (pushChar t h ψ) (AddMonoidAlgebra.single g 1) = ψ (AddMonoidAlgebra.single (fun i => ZMod.castHom h (ZMod m) (g i)) 1) := by
    intro ψ g
    simp [pushChar, AddMonoidAlgebra.mapDomainAlgHom_apply]
    rfl
  refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
  intro g
  rw [key, WithConv.ofConv_toConv, WithConv.ofConv_toConv, hmd, hmd, hmd, key]

theorem compat (σ : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R₀))
    {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R₀)) (L : RelativeGroupLaw R₀ g) (t : ℕ)
    (τ : SchemeHomOver (torusStr (ResidueField A) t)
      (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (residue A)) ≫ σ) g))
    (m m' : ℕ) (hm : 0 < m) (hm' : 0 < m') (h : m ∣ m')
    (ι : SchemeHomOver (muStr A t m) (RelativeGroupLaw.baseChangeStr σ g))
    (ι' : SchemeHomOver (muStr A t m') (RelativeGroupLaw.baseChangeStr σ g))
    (hι'mul : ∀ (S : Type u) [CommRing S] [Algebra A S] (χ χ' : WithConv (muCoord A t m' →ₐ[A] S)),
        NeronModelInfra.schemeHomOverComp (muPt A S t m' (χ * χ').ofConv) ι' =
          (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A S t m' χ.ofConv) ι')
            (NeronModelInfra.schemeHomOverComp (muPt A S t m' χ'.ofConv) ι'))
    (hι'sp : muBaseChange (residue A) t m' ≫ ι'.1 ≫ pullback.fst g σ =
        muToTorus (ResidueField A) t m' ≫ τ.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (residue A)) ≫ σ))
    (huniq : ∀ ι'' : SchemeHomOver (muStr A t m) (RelativeGroupLaw.baseChangeStr σ g),
        (∀ (S : Type u) [CommRing S] [Algebra A S] (χ χ' : WithConv (muCoord A t m →ₐ[A] S)),
          NeronModelInfra.schemeHomOverComp (muPt A S t m (χ * χ').ofConv) ι'' =
            (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A S t m χ.ofConv) ι'')
              (NeronModelInfra.schemeHomOverComp (muPt A S t m χ'.ofConv) ι'')) →
        (muBaseChange (residue A) t m ≫ ι''.1 ≫ pullback.fst g σ =
          muToTorus (ResidueField A) t m ≫ τ.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (residue A)) ≫ σ)) →
        ι'' = ι) :
    muIncl A t h ≫ ι'.1 = ι.1 := by
  let ι'' : SchemeHomOver (muStr A t m) (RelativeGroupLaw.baseChangeStr σ g) :=
    ⟨muIncl A t h ≫ ι'.1, by rw [Category.assoc, ι'.2, muIncl_comp_muStr]⟩
  have hc : ∀ (S : Type u) [CommRing S] [Algebra A S] (ψ : muCoord A t m →ₐ[A] S),
      NeronModelInfra.schemeHomOverComp (muPt A S t m ψ) ι'' =
        NeronModelInfra.schemeHomOverComp (muPt A S t m' (pushChar t h ψ)) ι' := by
    intro S _ _ ψ
    apply Subtype.ext
    rw [NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, muPt_pushChar, Category.assoc]
  have hmul : ∀ (S : Type u) [CommRing S] [Algebra A S] (χ χ' : WithConv (muCoord A t m →ₐ[A] S)),
      NeronModelInfra.schemeHomOverComp (muPt A S t m (χ * χ').ofConv) ι'' =
        (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A S t m χ.ofConv) ι'')
          (NeronModelInfra.schemeHomOverComp (muPt A S t m χ'.ofConv) ι'') := by
    intro S _ _ χ χ'
    rw [hc, hc, hc, pushChar_mul]
    exact hι'mul S _ _
  have hsp : muBaseChange (residue A) t m ≫ ι''.1 ≫ pullback.fst g σ =
      muToTorus (ResidueField A) t m ≫ τ.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (residue A)) ≫ σ) := by
    show muBaseChange (residue A) t m ≫ (muIncl A t h ≫ ι'.1) ≫ pullback.fst g σ = _
    rw [Category.assoc, ← Category.assoc, muBaseChange_comp_muIncl, Category.assoc, hι'sp, ← Category.assoc,
      muIncl_comp_muToTorus]
  exact congrArg Subtype.val (huniq ι'' hmul hsp)

end TLGlue

end glue

section head
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)

    {G : Scheme.{0}} (g : G ⟶ base p) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (L : RelativeGroupLaw (baseRing p) g) (hcomm : L.IsCommutative)

    (nsmul_flat : ∀ n : ℕ, 0 < n → Flat (L.schemeNsmul n))
    (nsmul_locallyQuasiFinite : ∀ n : ℕ, 0 < n → LocallyQuasiFinite (L.schemeNsmul n))

    (A : ValuationSubring (AlgebraicClosure ℚ)) (Λ : JHNeronObjectAtP.LevelData p M H hpM A)

    (pts : JH M H ≃ SchemeHomOver (genPt p) g)
    (hpts_add : ∀ x y : JH M H, pts (x + y) = L.mul _ (pts x) (pts y))
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JH M H),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)

    (toricRank : ℕ)
    (torusFibre : SchemeHomOver (torusStr (ResidueField ↥A) toricRank)
      (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g))
    (torusFibre_isClosedImmersion : IsClosedImmersion torusFibre.1)
    (torusFibre_mul : ∀ χ χ' : WithConv (torusCoord (ResidueField ↥A) toricRank →ₐ[ResidueField ↥A] ResidueField ↥A),
      NeronModelInfra.schemeHomOverComp (torusPt _ _ (χ * χ').ofConv) torusFibre =
        (L.baseChange (resPt A ≫ Λ.σA)).mul _
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) torusFibre)
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ'.ofConv) torusFibre))

    (abqFibre : Fin 2 → SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g)
      (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f))
    (abqFibre_eq_one_iff : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ResidueField ↥A)))
      (x : SchemeHomOver s (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g)),
      (∀ i, NeronModelInfra.schemeHomOverComp x (abqFibre i) =
          (Λ.L.baseChange (resPt A ≫ Λ.σA)).one s) ↔
        ∃ y : SchemeHomOver s (torusStr (ResidueField ↥A) toricRank),
          NeronModelInfra.schemeHomOverComp y torusFibre = x)
    (abqFibre_twist : ∀ (β : SchemeHomOver (resPt A ≫ Λ.σA) (resPt A ≫ Λ.σA)) (i : Fin 2)
      (x : SchemeHomOver (resPt A ≫ Λ.σA) g),
      fibreMap (abqFibre i) (GoodReductionJacobian.schemeHomOverComp β.1 β.2 x) =
        GoodReductionJacobian.schemeHomOverComp β.1 β.2 (fibreMap (abqFibre i) x)) :
    ∃ toricLift : ∀ m : ℕ, 0 < m →
        SchemeHomOver (muStr ↥A toricRank m) (RelativeGroupLaw.baseChangeStr Λ.σA g),

      (∀ (m : ℕ) (hm : 0 < m), IsClosedImmersion (toricLift m hm).1) ∧

      (∀ (m : ℕ) (hm : 0 < m) (χ χ' : WithConv (muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ)),
        NeronModelInfra.schemeHomOverComp (muPt A toricRank m (χ * χ').ofConv) (toricLift m hm) =
          (L.baseChange Λ.σA).mul _
            (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ.ofConv) (toricLift m hm))
            (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ'.ofConv) (toricLift m hm))) ∧

      (∀ (m m' : ℕ) (hm : 0 < m) (hm' : 0 < m') (h : m ∣ m'),
        muIncl ↥A toricRank h ≫ (toricLift m' hm').1 = (toricLift m hm).1) ∧

      (∀ (m : ℕ) (hm : 0 < m),
        muBaseChange (residue ↥A) toricRank m ≫ (toricLift m hm).1 ≫ pullback.fst g Λ.σA =
          muToTorus (ResidueField ↥A) toricRank m ≫ torusFibre.1 ≫ pullback.fst g (resPt A ≫ Λ.σA)) ∧

      (∀ (m : ℕ) (hm : 0 < m), ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ c : ℕ,
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ m = 1 → σ ζ = ζ ^ c) →
        ∀ χ : muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
          σ • pts.symm (genOfBaseChangePt Λ.hσA
              (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ) (toricLift m hm))) =
            c • pts.symm (genOfBaseChangePt Λ.hσA
              (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ) (toricLift m hm)))) ∧

      (∀ (m : ℕ) (hm : 0 < m), ∀ σ ∈ A.decompositionSubgroup ℚ,
        ∀ χ : muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
          ∃ χ' : muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
            σ • pts.symm (genOfBaseChangePt Λ.hσA
                (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ) (toricLift m hm))) =
              pts.symm (genOfBaseChangePt Λ.hσA
                (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ') (toricLift m hm)))) := by

  haveI hA₁ : HenselianLocalRing ↥A := ValuationSubring.henselianLocalRing_of_isAlgClosed A
  haveI hA₂ : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A

  have hα : ∀ (m : ℕ) (hm : 0 < m), _ := fun m hm =>
    AlgebraicGeometry.SplitTorus.existsUnique_muLift_baseChange_of_torusFibre_of_henselian
      (σ := Λ.σA) g L hcomm m hm (nsmul_locallyQuasiFinite m hm) (nsmul_flat m hm)
      toricRank torusFibre torusFibre_isClosedImmersion torusFibre_mul
  refine ⟨fun m hm => (hα m hm).choose, fun m hm => (hα m hm).choose_spec.1.1, fun m hm χ χ' => ?_, ?_,
    fun m hm => (hα m hm).choose_spec.1.2.2, fun m hm => ?_, fun m hm => ?_⟩
  ·
    exact (hα m hm).choose_spec.1.2.1 (AlgebraicClosure ℚ) χ χ'
  ·
    intro m m' hm hm' h
    exact TLGlue.compat (σ := Λ.σA) g L toricRank torusFibre m m' hm hm' h (hα m hm).choose (hα m' hm').choose
      (hα m' hm').choose_spec.1.2.1 (hα m' hm').choose_spec.1.2.2 (hα m hm).choose_spec.2
  ·
    exact (ModularCurve.JHNeronObjectAtP.inertia_smul_eq_and_exists_decomposition_smul_eq_of_muLift p M H hpM g L hcomm
      nsmul_flat nsmul_locallyQuasiFinite A Λ pts hpts_add hpts_galois toricRank torusFibre torusFibre_isClosedImmersion
      torusFibre_mul abqFibre abqFibre_eq_one_iff abqFibre_twist m hm (hα m hm).choose (hα m hm).choose_spec.1.2.1
      (hα m hm).choose_spec.1.2.2).1
  ·
    exact (ModularCurve.JHNeronObjectAtP.inertia_smul_eq_and_exists_decomposition_smul_eq_of_muLift p M H hpM g L hcomm
      nsmul_flat nsmul_locallyQuasiFinite A Λ pts hpts_add hpts_galois toricRank torusFibre torusFibre_isClosedImmersion
      torusFibre_mul abqFibre abqFibre_eq_one_iff abqFibre_twist m hm (hα m hm).choose (hα m hm).choose_spec.1.2.1
      (hα m hm).choose_spec.1.2.2).2

end head

end S_ModularCurve_JHNeronObjectAtP_exists_toricLift_of_torusFibre
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_toricLift_of_torusFibre (solution)
