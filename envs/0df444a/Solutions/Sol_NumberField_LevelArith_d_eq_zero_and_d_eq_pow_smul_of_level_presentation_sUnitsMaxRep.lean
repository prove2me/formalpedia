-- Prove2me | solution 1 for NumberField.LevelArith.d_eq_zero_and_d_eq_pow_smul_of_level_presentation_sUnitsMaxRep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a0ca942a-27b7-556e-8250-6a0dd923135c

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_d_eq_zero_and_d_eq_pow_smul_of_level_presentation_sUnitsMaxRep

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain NumberField.LevelArith
open scoped NumberField.LevelArith

theorem solution
    {p : ℕ} (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ ↥F]
    (u : (Fin 3 → ↥L.fixingSubgroup) → sUnitsMaxRep S L) (w₀ : (Fin 2 → ↥L.fixingSubgroup) → sUnitsMaxRep S L)
    (f : (Fin 3 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) (b₀ : (Fin 2 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hu : ∀ g : Fin 3 → ↥L.fixingSubgroup, u g = ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L))
    (hw : ∀ g : Fin 2 → ↥L.fixingSubgroup, w₀ g = ((b₀ (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L))
    (k : ℕ) :
    ((((inhomogeneousCochains (sUnitsMaxRep S L)).d 3 4).hom u = 0) → ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 3 4).hom f = 0) ∧
    ((((inhomogeneousCochains (sUnitsMaxRep S L)).d 2 3).hom w₀ = (p ^ k : ℤ) • u) →
      ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 2 3).hom b₀ = (p ^ k : ℤ) • f) := by

  let φ : Rep.res (QuotientGroup.mk' (F.fixingSubgroup.comap L.fixingSubgroup.subtype))
      ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶ sUnitsMaxRep S L :=
    Rep.ofHom ((sUnitsMaxRep S L).ρ.quotientToInvariants_lift (F.fixingSubgroup.comap L.fixingSubgroup.subtype))
  haveI hmono : Mono φ := (Rep.mono_iff_injective _).2 Subtype.val_injective
  let ι := groupCohomology.cochainsMap (QuotientGroup.mk' (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) φ
  have hinj : ∀ i, Function.Injective (ι.f i).hom := fun i =>
    (ModuleCat.mono_iff_injective _).1
      (groupCohomology.cochainsMap_f_map_mono _ _ (QuotientGroup.mk'_surjective _) i)
  have hcomm : ∀ (i j : ℕ) x, ((inhomogeneousCochains (sUnitsMaxRep S L)).d i j).hom ((ι.f i).hom x) =
      (ι.f j).hom (((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants
        (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d i j).hom x) := fun i j x => by
    have := ι.comm i j
    exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom this) x)
  have huf : u = (ι.f 3).hom f := funext fun g => hu g
  have hwb : w₀ = (ι.f 2).hom b₀ := funext fun g => hw g
  refine ⟨fun h => hinj 4 ?_, fun h => hinj 3 ?_⟩
  · rw [← hcomm, ← huf, h, map_zero]
  · rw [← hcomm, ← hwb, h, map_zsmul, ← huf]

end S_NumberField_LevelArith_d_eq_zero_and_d_eq_pow_smul_of_level_presentation_sUnitsMaxRep
end P2MW
export P2MW.S_NumberField_LevelArith_d_eq_zero_and_d_eq_pow_smul_of_level_presentation_sUnitsMaxRep (solution)
