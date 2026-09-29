-- Prove2me | solution 1 for NumberField.LevelArith.exists_three_cochain_val_eq_of_le_sUnitsMaxRep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f069c23a-4c3a-5719-933d-75ddfbb1d633

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Theorems.Thm_NumberField_LevelArith_sUnitsMaxStable_eq_sUnitsMax
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_three_cochain_val_eq_of_le_sUnitsMaxRep

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain NumberField.LevelArith
open scoped NumberField.LevelArith

theorem solution
    {p : ℕ} (S : Finset Nat.Primes) (L L' F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL' : L ≤ L') (hL'F : L' ≤ F)
    [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    (f : (Fin 3 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (k : ℕ) (b₀ : (Fin 2 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hk : ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 2 3).hom b₀ = (p ^ k : ℤ) • f) :
    ∃ (f' : (Fin 3 → (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype))) (b₀' : (Fin 2 → (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype))),
      (((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 3 4).hom f = 0 → ((inhomogeneousCochains ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype))).d 3 4).hom f' = 0) ∧
      ((inhomogeneousCochains ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype))).d 2 3).hom b₀' = (p ^ k : ℤ) • f' ∧
      (∀ (g : Fin 3 → ↥L'.fixingSubgroup) (g₀ : Fin 3 → ↥L.fixingSubgroup),
        (∀ i, ((g₀ i : ↥L.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = ((g i : ↥L'.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) →
        ((sUnitsMaxRep.val S L' ((f' (fun i => (g i : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))) : (sUnitsMaxRep S L').quotientToInvariants _) : sUnitsMaxRep S L') : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
          = ((sUnitsMaxRep.val S L ((f (fun i => (g₀ i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) := by
  classical

  have hΓ : L'.fixingSubgroup ≤ L.fixingSubgroup := IntermediateField.fixingSubgroup_antitone hLL'
  let incl : ↥L'.fixingSubgroup →* ↥L.fixingSubgroup := Subgroup.inclusion hΓ
  have hU : F.fixingSubgroup.comap L'.fixingSubgroup.subtype ≤
      (F.fixingSubgroup.comap L.fixingSubgroup.subtype).comap incl := fun γ h => h
  let r : (↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype) →*
      (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype) :=
    QuotientGroup.map _ _ incl hU

  have hcar : sUnitsMaxSubmodule S L = sUnitsMaxSubmodule S L' := by
    ext x
    rw [mem_sUnitsMaxSubmodule, mem_sUnitsMaxSubmodule, sUnitsMaxStable_eq_sUnitsMax, sUnitsMaxStable_eq_sUnitsMax]

  have hvalinj : ∀ {x y : sUnitsMaxRep S L'}, sUnitsMaxRep.val S L' x = sUnitsMaxRep.val S L' y → x = y :=
    fun h => Subtype.ext (Additive.toMul.injective h)
  let τ : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) →ₗ[ℤ]
      ((sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype)) :=
    { toFun := fun v => ⟨⟨(v.1).1, hcar ▸ (v.1).2⟩, fun γ => by
        have h0 := congrArg (sUnitsMaxRep.val S L) (v.2 ⟨incl γ.1, hU γ.2⟩)
        rw [MonoidHom.comp_apply, sUnitsMaxRep.val_ρ] at h0
        apply hvalinj
        rw [MonoidHom.comp_apply, sUnitsMaxRep.val_ρ]
        exact h0⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hτ : ∀ v, sUnitsMaxRep.val S L' (τ v : sUnitsMaxRep S L') = sUnitsMaxRep.val S L (v : sUnitsMaxRep S L) :=
    fun _ => rfl

  let ψ : Rep.res r ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
      (sUnitsMaxRep S L').quotientToInvariants (F.fixingSubgroup.comap L'.fixingSubgroup.subtype) :=
    Rep.ofHom ⟨τ, fun q => QuotientGroup.induction_on q fun γ => LinearMap.ext fun v => rfl⟩
  let T := groupCohomology.cochainsMap r ψ
  have hcomm : ∀ (i j : ℕ) x,
      ((inhomogeneousCochains ((sUnitsMaxRep S L').quotientToInvariants
        (F.fixingSubgroup.comap L'.fixingSubgroup.subtype))).d i j).hom ((T.f i).hom x) =
      (T.f j).hom (((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants
        (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d i j).hom x) := fun i j x =>
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (T.comm i j)) x
  refine ⟨(T.f 3).hom f, (T.f 2).hom b₀, fun hf => ?_, ?_, fun g g₀ hg => ?_⟩
  · rw [hcomm, hf, map_zero]
  · rw [hcomm, hk, map_zsmul]
  ·
    have hq : ∀ i, r (g i : ↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype) =
        (g₀ i : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype) := fun i => by
      change (QuotientGroup.mk (incl (g i)) : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype) = _
      congr 1
      exact Subtype.ext (hg i).symm
    have hq' : (fun i => r (g i : ↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype)) =
        fun i => (g₀ i : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype) := funext hq
    show ((sUnitsMaxRep.val S L' ((τ (f (fun i => r (g i : ↥L'.fixingSubgroup ⧸ F.fixingSubgroup.comap L'.fixingSubgroup.subtype))) :
        (sUnitsMaxRep S L').quotientToInvariants _) : sUnitsMaxRep S L') : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = _
    rw [hq']
    exact congrArg Units.val (hτ _)

end S_NumberField_LevelArith_exists_three_cochain_val_eq_of_le_sUnitsMaxRep
end P2MW
export P2MW.S_NumberField_LevelArith_exists_three_cochain_val_eq_of_le_sUnitsMaxRep (solution)
