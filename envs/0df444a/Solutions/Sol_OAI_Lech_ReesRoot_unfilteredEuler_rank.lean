-- Prove2me | solution 1 for OAI.Lech.ReesRoot.unfilteredEuler_rank
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T23:37:15.361477+00:00
-- url     : https://prove2.me/submissions/302995e0-340a-46c5-bee1-537c80224ac5

import Mathlib
import Definitions.Def_OAIQ032L039
import Theorems.Thm_OAI_Lech_FiniteModuleCech_tensorEuler_copies
import Theorems.Thm_OAI_Lech_ReesRoot_unfilteredEuler_affine_step
import Theorems.Thm_OAI_Lech_ReesRoot_unfilteredEuler_diagonal
import Theorems.Thm_OAI_Lech_ReesRoot_unfilteredTotal_finite

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteComplexTopInclusion
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
namespace Lech

section


universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]


variable {R : Type u} [CommRing R] {I : Ideal R}
namespace TorsionLength
variable (ℓ : TorsionLength I)

lemma eq_of_iso {M N : ModuleCat.{u} R} (e : M ≅ N)
    (hM : powerTorsion I M) (hN : powerTorsion I N) : ℓ.value M = ℓ.value N :=
  le_antisymm (ℓ.le_of_mono e.hom hN) (ℓ.le_of_mono e.inv hM)

end TorsionLength
end


universe u
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredFractionReesDenominatorTheory
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian

open scoped BigOperators
namespace Lech


open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable {R : Type u} [CommRing R] {I : Ideal R} (ℓ : TorsionLength I)
variable (K L : CochainComplex (ModuleCat.{u} R) ℤ)
lemma finiteHomologyEuler_homologyIso (e : ∀ q,K.homology q ≅ L.homology q)
    (hK : ∀ q,powerTorsion I (K.homology q)) (m : ℤ) (N : ℕ) :
    finiteHomologyEuler ℓ K m N=finiteHomologyEuler ℓ L m N := by
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact congrArg ENNReal.toReal (ℓ.eq_of_iso (e (m+i)) (hK _) ((powerTorsion I).prop_of_iso (e (m+i)) (hK _)))
lemma finiteHomologyEuler_iso (e : K ≅ L)
    (hK : ∀ q,powerTorsion I (K.homology q)) (m : ℤ) (N : ℕ) :
    finiteHomologyEuler ℓ K m N=finiteHomologyEuler ℓ L m N :=
  finiteHomologyEuler_homologyIso ℓ K L (fun q => (homologyFunctor _ _ q).mapIso e) hK m N
end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorCechEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]


variable {D E G : Diagram R ι} (φ : Map D E) (ψ : Map E G)
  (hzero : ∀ s,φ.app s ≫ ψ.app s=0)


variable {I : Ideal R} (ell : TorsionLength I)

lemma tensorEuler_iso (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)
    {D E : Diagram R ι} (e : positiveComplex D ≅ positiveComplex E)
    (hD : ∀ q,ell.finiteClass ((tensorCech F D).homology q)) :
    tensorEuler ell F h D=tensorEuler ell F h E := by
  apply congrArg ((-1:ℝ)^h * ·)
  exact finiteHomologyEuler_iso ell _ _
    ((TensorTotal.Right.functor F).mapIso
      ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso e)) (fun q => (hD q).1) _ _
end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootEulerFunction
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits FiniteModuleCech ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (ell : TorsionLength I) (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)


variable [LinearOrder (Chart n)]
  (hgen : Ideal.span (Set.range z)=I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hflat : ∀ p,Module.Flat R (F.X p)) (hp : ∀ p,Module.Projective R (F.X p))
  (hfin : ∀ p,Module.Finite R (F.X p))
  (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)

include hgen hds hmu ha B hflat hp hfin hb hac in
lemma unfilteredEuler_permute (σ : Equiv.Perm (Fin n)) (m : Fin n → ℤ) :
    unfilteredEuler I z hz ell F h m=unfilteredEuler I z hz ell F h (permuteWeight n σ m) :=
  tensorEuler_iso ell F h (permuteCechIso I z hz σ m)
    (unfilteredTotal_finite I z hz F h m hgen ell hds hmu ha b B hflat hp hfin hb hac)
end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SymmetricAffine
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.IntegerWeights
open Function


lemma integer_affine_of_step (g : ℤ → ℝ)
    (hg : ∀ a,g a+g (a+2)=2*g (a+1)) (a : ℤ) :
    g a=g 0+(a:ℝ)*(g 1-g 0) := by
  have hs (a : ℤ) : g (a+1)-g a=g 1-g 0 := by
    induction a using Int.induction_on with
    | zero => simp
    | succ k ih =>
        have he := hg (k:ℤ)
        rw [show (k:ℤ)+1+1=k+2 by omega]
        linarith
    | pred k ih =>
        have he := hg (-(k:ℤ)-1)
        rw [show -(k:ℤ)-1+1= -k by omega]
        rw [show -(k:ℤ)-1+2= -k+1 by omega,
          show -(k:ℤ)-1+1= -k by omega] at he
        linarith
  induction a using Int.induction_on with
  | zero => simp
  | succ k ih =>
      have he := hs (k:ℤ)
      push_cast at *
      nlinarith
  | pred k ih =>
      have he := hs (-(k:ℤ)-1)
      rw [show -(k:ℤ)-1+1= -k by omega] at he
      push_cast at *
      nlinarith

lemma separatelyAffine_of_step {ι : Type*} [DecidableEq ι]
    (f : (ι → ℤ) → ℝ)
    (hf : ∀ m i,f m+f (Pi.single i 1+(Pi.single i 1+m))=2*f (Pi.single i 1+m)) :
    SeparatelyAffine f := by
  intro m i a
  apply integer_affine_of_step (fun t => f (update m i t))
  intro x
  have he (t : ℤ) : Pi.single i 1+update m i t=update m i (t+1) := by
    funext j
    by_cases hj : j=i
    · subst j; simp [add_comm]
    · simp [hj]
  simpa only [he,show x+1+1=x+2 by omega] using hf (update m i x) i

lemma affine_eq_sum_of_slopes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℤ) → ℝ) (hf : SeparatelyAffine f) (c : ℝ)
    (hc : ∀ m i,f (update m i 1)-f (update m i 0)=c) (m : ι → ℤ) :
    f m=f (fun _ => 0)+c*∑ i,(m i:ℝ) := by
  let v (s : Finset ι) : ι → ℤ := fun i => if i∈s then m i else 0
  have hv (s : Finset ι) : f (v s)=f (fun _ => 0)+c*∑ i∈s,(m i:ℝ) := by
    induction s using Finset.induction_on with
    | empty => simp [v]
    | @insert i s hi ih =>
        have he : v (insert i s)=update (v s) i (m i) := by
          funext j
          by_cases hj : j=i
          · subst j; simp [v]
          · simp [v,hj]
        have hzero : update (v s) i 0=v s := by
          have hv0 : v s i=0 := by simp [v,hi]
          rw [←hv0,update_eq_self]
        rw [he,hf (v s) i (m i),hc,hzero,ih,Finset.sum_insert hi]
        ring
  simpa [v] using hv Finset.univ

lemma cons_update_zero {n : ℕ} (m : Fin (n+1) → ℤ) (a : ℤ) :
    update m 0 a=Fin.cons a (Fin.tail m) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]

 

theorem symmetric_affine_diagonal_constant (n : ℕ) (f : (Fin n → ℤ) → ℝ)
    (hf : SeparatelyAffine f)
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) m,f (m ∘ σ)=f m)
    (hdiag : ∀ m,f (fun i => m i+1)=f m) :
    ∀ m,f m=f (fun _ => 0) := by
  induction n with
  | zero => intro m; congr 1; funext i; exact Fin.elim0 i
  | succ n ih =>
    let g : (Fin n → ℤ) → ℝ := fun m => f (Fin.cons 1 m)-f (Fin.cons 0 m)
    have hhead (m : Fin n → ℤ) (a : ℤ) :
        f (Fin.cons a m)=f (Fin.cons 0 m)+(a:ℝ)*g m := by
      simpa only [Fin.update_cons_zero] using hf (Fin.cons 0 m) 0 a
    have hg : SeparatelyAffine g := by
      intro m i a
      have h1 := hf (Fin.cons 1 m) i.succ a
      have h0 := hf (Fin.cons 0 m) i.succ a
      simp only [←Fin.cons_update] at h1 h0
      dsimp only [g]
      rw [h1,h0]
      ring
    have hgsym (σ : Equiv.Perm (Fin n)) (m : Fin n → ℤ) : g (m ∘ σ)=g m := by
      let σ' : Equiv.Perm (Fin (n+1)) := Equiv.Perm.decomposeFin.symm (0,σ)
      have he (a : ℤ) : Fin.cons a (m ∘ σ)=(Fin.cons a m) ∘ σ' := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [σ']
        · simp [σ']
      dsimp only [g]
      rw [he,he,hsym,hsym]
    have hgdiag (m : Fin n → ℤ) : g (fun i => m i+1)=g m := by
      have he (a : ℤ) : Fin.cons a (fun i => m i+1)=(fun (i : Fin (n+1)) => (Fin.cons (α := fun _ => ℤ) (a-(1:ℤ)) m i : ℤ)+(1:ℤ)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      dsimp only [g]
      rw [he,he,hdiag,hdiag]
      norm_num only [sub_self,zero_sub]
      rw [hhead m (-1)]
      dsimp only [g]
      norm_num
    have hgconst := ih g hg hgsym hgdiag
    let c := g (fun _ => 0)
    have hzero (m : Fin (n+1) → ℤ) : f (update m 0 1)-f (update m 0 0)=c := by
      rw [cons_update_zero,cons_update_zero]
      exact hgconst (Fin.tail m)
    have hc (m : Fin (n+1) → ℤ) (i : Fin (n+1)) :
        f (update m i 1)-f (update m i 0)=c := by
      let σ : Equiv.Perm (Fin (n+1)) := Equiv.swap 0 i
      calc
        _=f ((update m i 1) ∘ σ)-f ((update m i 0) ∘ σ) := by rw [hsym,hsym]
        _=f (update (m ∘ σ) 0 1)-f (update (m ∘ σ) 0 0) := by
          rw [update_comp_equiv,update_comp_equiv]
          simp [σ]
        _=c := hzero _
    have hformula := affine_eq_sum_of_slopes f hf c hc
    have hcone := hdiag (fun _ => 0)
    rw [hformula (fun _ => 0+1)] at hcone
    have hc0 : c=0 := by
      simp only [Int.cast_one,zero_add,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hcone
      have hn : (0:ℝ)<(n+1:ℕ) := Nat.cast_pos.mpr (by omega)
      nlinarith
    intro m
    rw [hformula m,hc0,zero_mul,add_zero]
end Lech.IntegerWeights

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootEulerConstant
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits FiniteModuleCech ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (ell : TorsionLength I) (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)
  [LinearOrder (Chart n)]
  (hgen : Ideal.span (Set.range z)=I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hflat : ∀ p,Module.Flat R (F.X p)) (hp : ∀ p,Module.Projective R (F.X p))
  (hfin : ∀ p,Module.Finite R (F.X p))
  (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)
  (hbr : ∑ k∈Finset.range (h+1),(-1:ℝ)^k*(b (-(h:ℤ)+k):ℝ)=0)

include hgen hds hmu ha B hflat hp hfin hb hac hbr in
 
theorem unfilteredEuler_constant (m m' : Fin n → ℤ) :
    unfilteredEuler I z hz ell F h m=unfilteredEuler I z hz ell F h m' := by
  have hc := IntegerWeights.symmetric_affine_diagonal_constant n (unfilteredEuler I z hz ell F h)
    (IntegerWeights.separatelyAffine_of_step _
      (unfilteredEuler_affine_step I z hz ell F h hgen hds hmu ha b B hflat hp hfin hb hac))
    (by
      intro σ w
      have he := unfilteredEuler_permute I z hz ell F h hgen hds hmu ha b B hflat hp hfin hb hac σ.symm w
      exact he.symm)
    (unfilteredEuler_diagonal I z hz ell F h hgen hds hmu ha b B hflat hp hfin hb hac hbr)
  exact (hc m).trans (hc m').symm
end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootEulerRank
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.UniversalSplitting
lemma powerIndex_card (n : ℕ) : Fintype.card (PowerIndex n)=n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Fintype.card (Fin (n+1) × PowerIndex n)=(n+1).factorial
      rw [Fintype.card_prod,Fintype.card_fin,ih,Nat.factorial_succ]
end Lech.UniversalSplitting
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits FiniteModuleCech ProductSourceCover UniversalSplitting
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (ell : TorsionLength I) (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)
  [LinearOrder (Chart n)]
  (hgen : Ideal.span (Set.range z)=I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hflat : ∀ p,Module.Flat R (F.X p)) (hp : ∀ p,Module.Projective R (F.X p))
  (hfin : ∀ p,Module.Finite R (F.X p))
  (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)
  (hbr : ∑ k∈Finset.range (h+1),(-1:ℝ)^k*(b (-(h:ℤ)+k):ℝ)=0)

include hgen hds hmu ha B hflat hp hfin hb hac hbr in
 

theorem unfilteredEuler_rank_oai (m : Fin n → ℤ) :
    unfilteredEuler I z hz ell F h m=
      (n.factorial:ℝ)*tensorEuler ell F h (scalarCechDiagram I z hz) := by
  have he : positiveComplex (cechDiagram I z hz (fun i => (powerWeight n i:ℤ))) ≅
      positiveComplex (copiesDiagram (scalarCechDiagram I z hz) (PowerIndex n)) :=
    (ulrichCechIso I z hz).trans (positiveIso (fun _ => LinearEquiv.refl R _) (fun _ _ => rfl))
  have hf (q : ℤ) := unfilteredTotal_finite I z hz F h
    (fun i => (powerWeight n i:ℤ)) hgen ell hds hmu ha b B hflat hp hfin hb hac q
  have hC (q : ℤ) : ell.finiteClass
      ((tensorCech F (copiesDiagram (scalarCechDiagram I z hz) (PowerIndex n))).homology q) :=
    ell.finiteClass.prop_of_iso ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).mapIso
      ((TensorTotal.Right.functor F).mapIso
        ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso he))) (hf q)
  have hk : Nonempty (PowerIndex n) := Fintype.card_pos_iff.mp (by rw [powerIndex_card]; exact Nat.factorial_pos n)
  rw [unfilteredEuler_constant I z hz ell F h hgen hds hmu ha b B hflat hp hfin hb hac hbr
    m (fun i => (powerWeight n i:ℤ))]
  unfold unfilteredEuler
  rw [tensorEuler_iso ell F h he hf,
    tensorEuler_copies (scalarCechDiagram I z hz) ell F h hb hflat hk.some hC,powerIndex_card]
end Lech.ReesRoot

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.ReesRoot.unfilteredEuler_rank_oai.{u} := @OAI.Lech.ReesRoot.unfilteredEuler_rank_oai.{u}
