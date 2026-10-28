-- Prove2me | solution 1 for OAI.Lech.ReesRoot.scalarEuler_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:37:31.947442+00:00
-- url     : https://prove2.me/submissions/125ca005-75bc-43ba-be69-aa3662f08e64

import Mathlib
import Definitions.Def_OAIQ032L029
import Theorems.Thm_OAI_Lech_FilteredCech_positive_homology_powerTorsion
import Theorems.Thm_OAI_Lech_ReesRoot_scalarHomology_value
import Theorems.Thm_OAI_Lech_SourceGraded_acyclicity_finite_torsion

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootEulerPositivity
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R] {I : Ideal R} (ell : TorsionLength I)

lemma finiteHomologyEuler_pure_zero (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ i : ℤ,i≠0 → ell.zeroClass (K.homology i)) (h N : ℕ) (hN : h≤N) :
    (-1:ℝ)^h * finiteHomologyEuler ell K (-(h:ℤ)) N=ell.realValue (K.homology 0) := by
  classical
  unfold finiteHomologyEuler
  rw [Finset.sum_eq_single h]
  · simp only [neg_add_cancel]
    rw [←mul_assoc,←pow_add,show h+h=2*h by omega,pow_mul]
    norm_num
  · intro j hj hjh
    have hz := (hK (-(h:ℤ)+j) (by omega)).2
    change ell.value (K.homology (-(h:ℤ)+j))=0 at hz
    simp only [TorsionLength.realValue,hz,ENNReal.toReal_zero,mul_zero]
  · intro hh
    exact (hh (Finset.mem_range.mpr (by omega))).elim

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarCechEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex FiniteModuleCech MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)


variable (F : CochainComplex (ModuleCat.{u} R) ℤ)

variable [Nontrivial R] (hgen : Ideal.span (Set.range z)=I)
  (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun j => z j^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (hK : ∀ a : ℕ,1≤a → ∀ i : ℤ,i<0 →
    ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
  (hf : ∀ p,Module.Free R (F.X p)) (hfin : ∀ p,Module.Finite R (F.X p))
  (hb : ∀ p,p < -(n+1:ℤ) ∨ 0<p → IsZero (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)

include hgen hds hmu ha hK hf hfin hb hac in
 
theorem scalarEuler_value_oai :
    tensorEuler ell F (n+1) (scalarCechDiagram I z hz)=ell.realValue (F.homology 0) := by
  have H := SourceGraded.acyclicity_finite_torsion I z hgen ell F hmu ha hK hf hfin
    (by simpa only [Nat.cast_add,Nat.cast_one] using hb) hac
  have hp : ∀ p,Module.Projective R (F.X p) := fun p => by have := hf p; infer_instance
  have ht (i : ℤ) : powerTorsion I ((tensorCech F (scalarCechDiagram I z hz)).homology i) :=
    (powerTorsion I).prop_of_iso (scalarHomologyIso I z hz F i).symm
      (FilteredCech.positive_homology_powerTorsion I z hz F (-(n+1:ℤ)) 0 hp hfin hb hac 0 (i+1))
  have he := finiteHomologyEuler_pure_zero ell (tensorCech F (scalarCechDiagram I z hz))
    (fun i hi => ⟨ht i, by rw [scalarHomology_value I z hz F hgen ell hds hmu ha hK hf hfin hb hac]; exact H.2 i hi⟩)
    (n+1) (n+1+Fintype.card (Fin (n+1))) (by omega)
  change tensorEuler ell F (n+1) (scalarCechDiagram I z hz)=_ at he
  rw [he]
  exact congrArg ENNReal.toReal (scalarHomology_value I z hz F hgen ell hds hmu ha hK hf hfin hb hac 0)
end Lech.ReesRoot

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.ReesRoot.scalarEuler_value_oai.{u} := @OAI.Lech.ReesRoot.scalarEuler_value_oai.{u}
