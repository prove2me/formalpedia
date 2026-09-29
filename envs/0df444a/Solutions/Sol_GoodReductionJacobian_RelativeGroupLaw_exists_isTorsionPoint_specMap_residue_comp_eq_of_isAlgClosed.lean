-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_isTorsionPoint_specMap_residue_comp_eq_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/07de1021-f321-5468-b823-21cd320a1fd4

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing
import Theorems.Thm_AlgHom_exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isTorsionPoint_specMap_residue_comp_eq_of_isAlgClosed
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace FinLift

variable {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
  {R' : Type} [CommRing R'] (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))

theorem baseChangePointToBase_nsmul (L : RelativeGroupLaw R f) {T : Scheme.{0}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (n : ℕ) (x : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr ι f)) :
    RelativeGroupLaw.baseChangePointToBase ι ((L.baseChange ι).nsmul t' n x) =
      L.nsmul _ n (RelativeGroupLaw.baseChangePointToBase ι x) := by
  induction n with
  | zero =>
      rw [RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.baseChangePointToBase_one]
  | succ n ih =>
      rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.baseChangePointToBase_mul, ih]

theorem isTorsionPoint_baseChange_iff (L : RelativeGroupLaw R f) {T : Scheme.{0}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (n : ℕ) (x : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr ι f)) :
    (L.baseChange ι).IsTorsionPoint t' n x ↔ L.IsTorsionPoint _ n (RelativeGroupLaw.baseChangePointToBase ι x) := by
  rw [RelativeGroupLaw.isTorsionPoint_def, RelativeGroupLaw.isTorsionPoint_def, ← baseChangePointToBase_nsmul,
    ← RelativeGroupLaw.baseChangePointToBase_one ι L t']
  constructor
  · intro h; rw [h]
  · intro h
    have := congrArg (RelativeGroupLaw.baseChangePointOfBase ι) h
    rwa [RelativeGroupLaw.baseChangePointOfBase_toBase, RelativeGroupLaw.baseChangePointOfBase_toBase] at this

end FinLift

theorem solution
    {R : Type} [CommRing R] {K : Type} [Field K] [IsAlgClosed K] (A : ValuationSubring K) [HenselianLocalRing ↥A]
    (ι : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of R))
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} [IsSeparated f] [LocallyOfFiniteType f]
    (L : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x)
    (n : ℕ)
    [LocallyQuasiFinite ((L.baseChange ι).schemeKerStr n)] [QuasiCompact ((L.baseChange ι).schemeKerStr n)]
    [Flat ((L.baseChange ι).schemeKerStr n)]
    (y : SchemeHomOver (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ ι) f)
    (hy : L.IsTorsionPoint (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ ι) n y) :
    ∃ s : SchemeHomOver ι f, L.IsTorsionPoint ι n s ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s.1 = y.1 := by
  classical

  have hrκ : Spec.map (CommRingCat.ofHom (algebraMap ↥A (IsLocalRing.ResidueField ↥A))) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) := rfl

  have hcommσ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥A))
      (x y : SchemeHomOver t (RelativeGroupLaw.baseChangeStr ι f)),
      (L.baseChange ι).mul t x y = (L.baseChange ι).mul t y x := by
    intro T t x y
    rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChange_mul, hcomm]
  haveI : IsSeparated (RelativeGroupLaw.baseChangeStr ι f) := by
    unfold RelativeGroupLaw.baseChangeStr; infer_instance
  haveI : LocallyOfFiniteType (RelativeGroupLaw.baseChangeStr ι f) := by
    unfold RelativeGroupLaw.baseChangeStr; infer_instance

  obtain ⟨H, _, _, hfin, hflat, -, j, e, -, -, -, -, he_coe, -, he_surj, -, he_nat⟩ :=
    RelativeGroupLaw.exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing (L.baseChange ι) hcommσ n
  haveI : Module.Finite ↥A H := hfin
  haveI : Module.Flat ↥A H := hflat

  let yσ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥A (IsLocalRing.ResidueField ↥A))))
      (RelativeGroupLaw.baseChangeStr ι f) :=
    RelativeGroupLaw.baseChangePointOfBase ι y
  have hyσ : (L.baseChange ι).IsTorsionPoint _ n yσ := by
    rw [FinLift.isTorsionPoint_baseChange_iff, RelativeGroupLaw.baseChangePointToBase_ofBase]
    exact hy

  haveI : Module.Finite ↥A (IsLocalRing.ResidueField ↥A) :=
    Module.Finite.of_surjective (Algebra.linearMap ↥A (IsLocalRing.ResidueField ↥A)) Ideal.Quotient.mk_surjective
  obtain ⟨χ, hχ⟩ := he_surj (IsLocalRing.ResidueField ↥A) ⟨yσ, hyσ⟩

  obtain ⟨φ, hφ⟩ :=
    AlgHom.exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing ↥A K H χ.ofConv

  let sσ := e ↥A (WithConv.toConv φ)
  let s₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥A ↥A)) ≫ ι) f :=
    RelativeGroupLaw.baseChangePointToBase ι sσ.val
  have hs₀ : L.IsTorsionPoint _ n s₀ := by
    rw [← FinLift.isTorsionPoint_baseChange_iff]; exact sσ.2

  have hid : Spec.map (CommRingCat.ofHom (algebraMap ↥A ↥A)) = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom (RingHom.id ↥A)) = 𝟙 _
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  let s : SchemeHomOver ι f :=
    schemeHomOverComp (𝟙 _) (by rw [Category.id_comp, hid, Category.id_comp]) s₀
  have hs : L.IsTorsionPoint ι n s := L.isTorsionPoint_schemeHomOverComp _ _ _ _ n hs₀
  refine ⟨s, hs, ?_⟩

  have hnat := he_nat ↥A (IsLocalRing.ResidueField ↥A) (Algebra.ofId ↥A (IsLocalRing.ResidueField ↥A)) (WithConv.toConv φ)
  have hcomp : (Algebra.ofId ↥A (IsLocalRing.ResidueField ↥A)).comp φ = χ.ofConv := by
    ext h; exact hφ h
  have hcomp' : WithConv.toConv ((Algebra.ofId ↥A (IsLocalRing.ResidueField ↥A)).comp (WithConv.toConv φ).ofConv) = χ := by
    show WithConv.toConv ((Algebra.ofId ↥A (IsLocalRing.ResidueField ↥A)).comp φ) = χ
    rw [hcomp]
  rw [hcomp', hχ] at hnat

  have h1 : s.1 = s₀.1 := Category.id_comp _
  have h2 : s₀.1 = sσ.val.1 ≫ pullback.fst f ι := rfl
  have h3 : y.1 = yσ.1 ≫ pullback.fst f ι :=
    (congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_ofBase ι y)).symm
  have h4 : Spec.map (CommRingCat.ofHom (Algebra.ofId ↥A (IsLocalRing.ResidueField ↥A)).toRingHom) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) := rfl
  rw [h1, h2, h3, ← Category.assoc]
  congr 1
  rw [← h4]
  exact hnat.symm

#print axioms solution

end S_GoodReductionJacobian_RelativeGroupLaw_exists_isTorsionPoint_specMap_residue_comp_eq_of_isAlgClosed
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isTorsionPoint_specMap_residue_comp_eq_of_isAlgClosed (solution)
