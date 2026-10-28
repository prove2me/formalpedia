-- Prove2me | solution 1 for OAI.Lech.ReesRoot.unfilteredTotal_finite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:50:33.966978+00:00
-- url     : https://prove2.me/submissions/fbbbd4d8-a2cf-430b-91d7-13071ed3d143

import Mathlib
import Definitions.Def_OAIQ032L038
import Theorems.Thm_OAI_Lech_ReesRoot_enlargedAtTotal_finite

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootUnfiltered
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ) (m : Fin n → ℤ)


variable [LinearOrder (ProductSourceCover.Chart n)]
  (hgen : Ideal.span (Set.range z)=I)
  (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hflat : ∀ p,Module.Flat R (F.X p)) (hp : ∀ p,Module.Projective R (F.X p))
  (hfin : ∀ p,Module.Finite R (F.X p))
  (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)

include hgen hds hmu ha B hflat hp hfin hb hac in
 

lemma unfilteredTotal_finite_oai (i : ℤ) :
    ell.finiteClass (((TensorTotal.Right.functor F).obj (cechZ I z hz m)).homology i) := by
  have hf := enlargedAtTotal_finite I z hz F h 0 (IdealFiltered.zero_order_bound I F) m
    hgen hflat ell hds hmu ha b B hp hfin hb hac i
  exact (ell.finiteClass).prop_of_iso ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso
    (zeroOrderTotalIso I z hz F h m)) hf
end Lech.ReesRoot

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.ReesRoot.unfilteredTotal_finite_oai.{u} := @OAI.Lech.ReesRoot.unfilteredTotal_finite_oai.{u}
