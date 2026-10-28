-- Prove2me | solution 1 for OAI.Lech.null_projector_contractible_splitting
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:57:41.341558+00:00
-- url     : https://prove2.me/submissions/0283bbd2-789b-4dcb-a9b9-8c2f10856f46

import Mathlib

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ContractibleRetract
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R]

lemma split_contractible_retract (F K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a : K ⟶ F) (b : F ⟶ K) (hab : a ≫ b = 𝟙 K)
    (hK : Homotopy (𝟙 K) 0) :
    ∃ (G : CochainComplex (ModuleCat.{u} R) ℤ) (i : G ⟶ F) (r : F ⟶ G),
      i ≫ r = 𝟙 G ∧ r ≫ i + b ≫ a = 𝟙 F ∧ i ≫ b = 0 ∧ a ≫ r = 0 ∧
      Nonempty (HomotopyEquiv F G) := by
  have hq : (b ≫ a) ≫ (b ≫ a) = b ≫ a := by rw [Category.assoc,← Category.assoc a,hab,Category.id_comp]
  have hp : (𝟙 F - b ≫ a) ≫ (𝟙 F - b ≫ a) = 𝟙 F - b ≫ a :=
    CategoryTheory.Idempotents.idem_of_id_sub_idem _ hq
  obtain ⟨G,i,r,hir,hri⟩ := IsIdempotentComplete.idempotents_split F _ hp
  have hib : i ≫ b = 0 := by
    have he : i ≫ (r ≫ i) = i := by simp [← Category.assoc,hir]
    have hpb : (𝟙 F - b ≫ a) ≫ b = 0 := by simp [sub_comp,Category.assoc,hab]
    rw [← he,hri,Category.assoc,hpb,comp_zero]
  have har : a ≫ r = 0 := by
    have he : (r ≫ i) ≫ r = r := by simp [Category.assoc,hir]
    have hap : a ≫ (𝟙 F - b ≫ a) = 0 := by simp [comp_sub,← Category.assoc,hab]
    rw [← he,hri,← Category.assoc,hap,zero_comp]
  have hnull : Homotopy (b ≫ a) 0 := by simpa using (hK.compLeft b).compRight a
  have hh : Homotopy (r ≫ i) (𝟙 F) := by
    rw [hri]
    simpa [sub_eq_add_neg] using (Homotopy.refl (𝟙 F)).add (hnull.smul (-1:ℤ))
  exact ⟨G,i,r,hir,by rw [hri]; abel,hib,har,
    ⟨⟨r,i,hh,Homotopy.ofEq hir⟩⟩⟩


end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteFreeRetract
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]

omit [IsLocalRing R] in
lemma null_projector_contractible_splitting_oai
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (q : F ⟶ F)
    (hq : q ≫ q = q) (hn : Homotopy q 0) :
    ∃ (G K : CochainComplex (ModuleCat.{u} R) ℤ)
      (i : G ⟶ F) (r : F ⟶ G) (a : K ⟶ F) (b : F ⟶ K),
      i ≫ r = 𝟙 G ∧ a ≫ b = 𝟙 K ∧ b ≫ a = q ∧
      r ≫ i + b ≫ a = 𝟙 F ∧ i ≫ b = 0 ∧ a ≫ r = 0 ∧
      Nonempty (HomotopyEquiv F G) := by
  obtain ⟨K,a,b,hab,hba⟩ := IsIdempotentComplete.idempotents_split F q hq
  have hK : Homotopy (𝟙 K) 0 := by
    have he : a ≫ q ≫ b = 𝟙 K := by simp only [← hba,Category.assoc,hab,Category.comp_id]
    have hn' := (hn.compLeft a).compRight b
    simpa only [Category.assoc,he,comp_zero,zero_comp] using hn'
  obtain ⟨G,i,r,hir,hs,hib,har,he⟩ := split_contractible_retract F K a b hab hK
  exact ⟨G,K,i,r,a,b,hir,hab,hba,hs,hib,har,he⟩
end Lech

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.null_projector_contractible_splitting_oai.{u} := @OAI.Lech.null_projector_contractible_splitting_oai.{u}
