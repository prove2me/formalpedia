-- Prove2me | solution 1 for OAI.ReverseLogKodaira.LogarithmicSpecialization.logarithmic_specialization_equation_independent
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:21:35.100953+00:00
-- url     : https://prove2.me/submissions/3ebd0234-8945-4a83-a1a1-eb6aee6b3d1f

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/Specialization.lean:L352-L406
-- (upload_full_project.md Phase 4): solution for node OAI.ReverseLogKodaira.LogarithmicSpecialization.logarithmic_specialization_equation_independent. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Specialization

-- ---- from OAI.AlgebraicGeometry.LogKodaira.Specialization ----
namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.CanonicalSpecialization
open DifferentialBaseChange BasedRelativeCanonical

 
end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.CanonicalSpecialization
open DifferentialBaseChange BasedRelativeCanonical

 

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.FractionalCanonical
open CanonicalAdjunction DifferentialBaseChange BasedRelativeCanonical

lemma exists_absolute_basis
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FormallySmooth A B] (n r : ℕ)
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) :
    Nonempty (Module.Basis (Fin (n + r)) B (KaehlerDifferential R B)) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    (KaehlerDifferential.map R A B B) LinearMap.id (KaehlerDifferential.map_surjective R A B)
  exact ⟨(adaptedBasis (KaehlerDifferential.mapBaseChange R A B)
    (KaehlerDifferential.map R A B B) s (formallySmooth_mapBaseChange_injective R A B)
    (KaehlerDifferential.exact_mapBaseChange_map R A B) hs (b.baseChange B) c).reindex
      finSumFinEquiv⟩

lemma free_pluricanonical_injective
    (R B K : Type*) [CommRing R] [CommRing B] [Field K]
    [Algebra R B] [Algebra B K] [Algebra R K] [IsScalarTower R B K]
    [IsDomain B] [IsFractionRing B K] [Module.Free B (KaehlerDifferential R B)]
    (n m : ℕ) : Function.Injective (pluricanonicalMap R R B K n m) := by
  classical
  let := Algebra.FormallyEtale.of_isLocalization (Rₘ := K) (nonZeroDivisors B)
  let b := Module.Free.chooseBasis B (KaehlerDifferential R B)
  let : LinearOrder (Module.Free.ChooseBasisIndex B (KaehlerDifferential R B)) :=
    linearOrderOfSTO WellOrderingRel
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B K
  let c := (b.baseChange K).map e
  have hc (i) : c i = KaehlerDifferential.map R R B K (b i) := by
    simp [c, e, Module.Basis.baseChange_apply,
      KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul]
  have hw (s) : exteriorDifferentialMap R R B K n (b.exteriorPower n s) =
      c.exteriorPower n s := by
    simp only [exteriorPower.coe_basis, exteriorPower.ιMulti_family,
      exteriorDifferentialMap, exteriorScalarMap_wedge]
    congr 1
    funext i
    exact (hc _).symm
  let bb := Basis.piTensorProduct (fun _ : Fin m => b.exteriorPower n)
  let cc := Basis.piTensorProduct (fun _ : Fin m => c.exteriorPower n)
  have hh : (pluricanonicalMap R R B K n m) ∘ bb = cc := by
    funext s
    simp only [Function.comp_apply, bb, cc, Basis.piTensorProduct_apply,
      pluricanonicalMap, tensorScalarMap, PiTensorProduct.lift.tprod,
      MultilinearMap.compLinearMap_apply, hw]
    rfl
  have hli : LinearIndependent B ((pluricanonicalMap R R B K n m) ∘ bb) := by
    rw [hh]
    exact cc.linearIndependent.restrict_scalars' B
  have heq : bb.constr B ((pluricanonicalMap R R B K n m) ∘ bb) =
      pluricanonicalMap R R B K n m := by
    apply bb.ext
    intro i
    simp
  rw [← heq]
  exact bb.injective_constr_of_linearIndependent hli

 

theorem based_pluricanonical_injective
    (R A B K : Type*) [CommRing R] [CommRing A] [CommRing B] [Field K]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra B K] [Algebra R K] [IsScalarTower R B K]
    [IsDomain B] [IsFractionRing B K] [Algebra.FormallySmooth A B]
    (n r m : ℕ) (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) :
    Function.Injective (pluricanonicalMap R R B K (n + r) m) := by
  obtain ⟨d⟩ := exists_absolute_basis R A B n r b c
  let : Module.Free B (KaehlerDifferential R B) := Module.Free.of_basis d
  exact free_pluricanonical_injective R B K (n + r) m

end ReverseLogKodaira.FractionalCanonical

namespace ReverseLogKodaira.LogarithmicSpecialization
open DifferentialBaseChange BasedRelativeCanonical CanonicalSpecialization FractionalCanonical

 

 

end ReverseLogKodaira.LogarithmicSpecialization

namespace ReverseLogKodaira.LogarithmicSpecialization
open DifferentialBaseChange BasedRelativeCanonical CanonicalSpecialization FractionalCanonical

 

end ReverseLogKodaira.LogarithmicSpecialization

namespace ReverseLogKodaira.LogarithmicSpecialization
open DifferentialBaseChange BasedRelativeCanonical CanonicalSpecialization FractionalCanonical

 

theorem logarithmic_specialization_equation_independent
    (R A B K S C : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Field K] [CommRing S] [Field C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra B K] [Algebra R K] [IsScalarTower R B K]
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A S C]
    [IsDomain B] [IsFractionRing B K] [Algebra.FormallySmooth A B]
    (n r m : ℕ) (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) (t v : B)
    (ht : algebraMap B C t ≠ 0) (hv : algebraMap B C v ≠ 0)
    (u w : Pluricanonical R B (n + r) m)
    (heq : logarithmicPullback R B K (n + r) m t u =
      logarithmicPullback R B K (n + r) m v w) :
    logarithmicSpecialize R A B S C n r m b c t u =
      logarithmicSpecialize R A B S C n r m b c v w := by
  have htB : t ≠ 0 := by intro h; apply ht; simp [h]
  have hvB : v ≠ 0 := by intro h; apply hv; simp [h]
  have htK : algebraMap B K t ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective B K).ne htB
  have hvK : algebraMap B K v ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective B K).ne hvB
  have h1 : pluricanonicalMap R R B K (n + r) m u =
      (algebraMap B K t)^m •
        ((algebraMap B K v)^m)⁻¹ • pluricanonicalMap R R B K (n + r) m w :=
    (inv_smul_eq_iff₀ (pow_ne_zero m htK)).mp heq
  have hcross : v^m • u = t^m • w := by
    apply based_pluricanonical_injective R A B K n r m b c
    simp only [map_smul]
    rw [← IsScalarTower.algebraMap_smul K (v^m),
      ← IsScalarTower.algebraMap_smul K (t^m), map_pow, map_pow]
    calc
      (algebraMap B K v)^m • pluricanonicalMap R R B K (n + r) m u =
          (algebraMap B K v)^m • ((algebraMap B K t)^m •
            ((algebraMap B K v)^m)⁻¹ • pluricanonicalMap R R B K (n + r) m w) :=
        congrArg ((algebraMap B K v)^m • ·) h1
      _ = (algebraMap B K t)^m •
          ((algebraMap B K v)^m • ((algebraMap B K v)^m)⁻¹ •
            pluricanonicalMap R R B K (n + r) m w) := smul_comm _ _ _
      _ = (algebraMap B K t)^m • pluricanonicalMap R R B K (n + r) m w := by
        rw [smul_inv_smul₀ (pow_ne_zero m hvK)]
  have hc := congrArg (specializePluricanonical R A B S C n r m b c) hcross
  simp only [map_smul] at hc
  rw [← IsScalarTower.algebraMap_smul C (v^m),
    ← IsScalarTower.algebraMap_smul C (t^m), map_pow, map_pow] at hc
  apply smul_right_injective _ (mul_ne_zero (pow_ne_zero m ht) (pow_ne_zero m hv))
  simp only [logarithmicSpecialize, LinearMap.smul_apply, smul_smul]
  have htc : ((algebraMap B C t)^m * (algebraMap B C v)^m) *
      ((algebraMap B C t)^m)⁻¹ = (algebraMap B C v)^m := by
    field_simp
  have hvc : ((algebraMap B C t)^m * (algebraMap B C v)^m) *
      ((algebraMap B C v)^m)⁻¹ = (algebraMap B C t)^m := by
    field_simp
  rw [htc, hvc]
  exact hc

end ReverseLogKodaira.LogarithmicSpecialization

end

end OAI

-- ---- platform node ----
open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.LogarithmicSpecialization
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open DifferentialBaseChange BasedRelativeCanonical CanonicalSpecialization

theorem solution
    (R A B K S C : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Field K] [CommRing S] [Field C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra B K] [Algebra R K] [IsScalarTower R B K]
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A S C]
    [IsDomain B] [IsFractionRing B K] [Algebra.FormallySmooth A B]
    (n r m : ℕ) (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) (t v : B)
    (ht : algebraMap B C t ≠ 0) (hv : algebraMap B C v ≠ 0)
    (u w : Pluricanonical R B (n + r) m)
    (heq : logarithmicPullback R B K (n + r) m t u =
      logarithmicPullback R B K (n + r) m v w) :
    logarithmicSpecialize R A B S C n r m b c t u =
      logarithmicSpecialize R A B S C n r m b c v w := by
  first
    | exact OAI.ReverseLogKodaira.LogarithmicSpecialization.logarithmic_specialization_equation_independent R A B K S C n r m b c t v ht hv u w heq
    | exact OAI.ReverseLogKodaira.LogarithmicSpecialization.logarithmic_specialization_equation_independent
    | (apply OAI.ReverseLogKodaira.LogarithmicSpecialization.logarithmic_specialization_equation_independent <;> assumption)
    | (intros; apply OAI.ReverseLogKodaira.LogarithmicSpecialization.logarithmic_specialization_equation_independent <;> assumption)
