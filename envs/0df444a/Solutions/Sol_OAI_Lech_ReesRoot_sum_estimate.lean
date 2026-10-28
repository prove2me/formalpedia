-- Prove2me | solution 1 for OAI.Lech.ReesRoot.sum_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:53:25.563756+00:00
-- url     : https://prove2.me/submissions/40abae42-4aec-45e5-9115-e8a4755ab4a1

import Mathlib
import Definitions.Def_OAIQ032L038
import Theorems.Thm_OAI_Lech_ReesRoot_ambientStrip_euler
import Theorems.Thm_OAI_Lech_ReesRoot_ambient_euler_additive
import Theorems.Thm_OAI_Lech_ReesRoot_enlargedAtTotal_finite
import Theorems.Thm_OAI_Lech_ReesRoot_quotientAtTotal_euler
import Theorems.Thm_OAI_Lech_ReesRoot_rootTotal_pure
import Theorems.Thm_OAI_Lech_ReesRoot_scalarEuler_value
import Theorems.Thm_OAI_Lech_ReesRoot_unfilteredEuler_rank

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

namespace ReesRoot
open ProductSourceCover
variable (I : Ideal R) {n : ℕ} [LinearOrder (Chart n)]
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (hgen : Ideal.span (Set.range z)=I)
  (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hflat : ∀ p,Module.Flat R (F.X p)) (hp : ∀ p,Module.Projective R (F.X p))
  (hfin : ∀ p,Module.Finite R (F.X p))
  (hb : ∀ p,p < -(n+1:ℤ) ∨ 0<p → IsZero (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)

include hgen hds hmu ha B hflat hp hfin hb hac in
 

theorem rootTotal_euler_nonnegative (r : Fin n → ℤ) (hr : RootPositions n s r)
    (N : ℕ) (hN : n+1≤N) :
    let D := (enlargedAt I z hz F (n+1) s hd (rootAmbient s r 0)).total (.up ℤ)
    (∀ i,ell.finiteClass (D.homology i)) ∧
      (-1:ℝ)^(n+1)*finiteHomologyEuler ell D (-(n+1:ℤ)) N=ell.realValue (D.homology 0) ∧
      0≤(-1:ℝ)^(n+1)*finiteHomologyEuler ell D (-(n+1:ℤ)) N := by
  dsimp only
  have he := finiteHomologyEuler_pure_zero ell _
    (rootTotal_pure I z hz hgen ell hds hmu ha F s hd b B hflat hp hfin hb hac r hr) (n+1) N hN
  simp only [Nat.cast_add,Nat.cast_one] at he
  refine ⟨?_,he,?_⟩
  · intro i
    exact enlargedAtTotal_finite I z hz F (n+1) s hd _ hgen hflat ell hds hmu ha b B hp hfin hb hac i
  · rw [he]
    exact ENNReal.toReal_nonneg
end ReesRoot
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootStripComplement
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProductSourceCover
open scoped BigOperators

lemma rootPrefix_split (n : ℕ) (r : Fin n → ℤ) (h s k : ℕ) (hk : k≤h) :
    rootPrefix n r h s (k*s)+rootStripPolynomial n r (h-k) s=rootStripPolynomial n r h s := by
  unfold rootPrefix rootStripPolynomial
  rw [show h*s=k*s+(h-k)*s by rw [←Nat.add_mul]; congr 1; omega,Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.prod_congr rfl
  intro j hj
  rw [Nat.cast_sub hk]
  push_cast
  ring

lemma signed_reverse (h : ℕ) (b : ℤ → ℝ) (f : ℕ → ℝ) :
    (-1:ℝ)^h*(∑ k∈Finset.range (h+1),(-1:ℝ)^k*b (-(h:ℤ)+k)*f (h-k))=
      ∑ i∈Finset.range (h+1),(-1:ℝ)^i*b (-(i:ℤ))*f i := by
  rw [Finset.mul_sum,←Finset.sum_range_reflect
    (fun i => (-1:ℝ)^i*b (-(i:ℤ))*f i) (h+1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k≤h := by have := Finset.mem_range.mp hk; omega
  have he : h+1-1-k=h-k := by omega
  rw [he]
  have hp : -(h:ℤ)+(k:ℤ) = -((h-k:ℕ):ℤ) := by omega
  have hs : (-1:ℝ)^h*(-1:ℝ)^k=(-1:ℝ)^(h-k) := by
    conv_lhs => rw [show h=(h-k)+k by omega,pow_add]
    have hsq : (-1:ℝ)^k*(-1:ℝ)^k=1 := by rw [←mul_pow]; norm_num
    rw [mul_assoc,hsq,mul_one]
  rw [hp,←mul_assoc,←mul_assoc,hs]

lemma complement_euler (n : ℕ) (r : Fin n → ℤ) (h s : ℕ) (b : ℤ → ℝ)
    (hb : ∑ k∈Finset.range (h+1),(-1:ℝ)^k*b (-(h:ℤ)+k)=0) :
    (-1:ℝ)^h*(∑ k∈Finset.range (h+1),(-1:ℝ)^k*b (-(h:ℤ)+k)*
      rootPrefix n r h s (k*s))=
        -(∑ i∈Finset.range (h+1),(-1:ℝ)^i*b (-(i:ℤ))*rootStripPolynomial n r i s) := by
  have he : (∑ k∈Finset.range (h+1),(-1:ℝ)^k*b (-(h:ℤ)+k)*rootPrefix n r h s (k*s))=
      -(∑ k∈Finset.range (h+1),(-1:ℝ)^k*b (-(h:ℤ)+k)*rootStripPolynomial n r (h-k) s) := by
    calc
      _=∑ k∈Finset.range (h+1),(-1:ℝ)^k*b (-(h:ℤ)+k)*
          (rootStripPolynomial n r h s-rootStripPolynomial n r (h-k) s) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [eq_sub_iff_add_eq.mpr (rootPrefix_split n r h s k (by have := Finset.mem_range.mp hk; omega))]
      _=_ := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib,←Finset.sum_mul,hb,zero_mul,zero_sub]
  rw [he,mul_neg]
  exact congrArg Neg.neg (signed_reverse h b (fun i => rootStripPolynomial n r i s))
end Lech.ProductSourceCover

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SumEstimate
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover FiniteModuleCech
universe u
variable {R : Type u} [CommRing R] [Nontrivial R] (I : Ideal R) {n : ℕ}
  [LinearOrder (Chart n)]
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (hgen : Ideal.span (Set.range z)=I)
  (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun j => z j^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (hK : ∀ a : ℕ,1≤a → ∀ i : ℤ,i<0 →
    ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (s : ℕ)
  (hd : ∀ p : ℤ,(F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hf : ∀ p,Module.Free R (F.X p)) (hfin : ∀ p,Module.Finite R (F.X p))
  (hb : ∀ p,p < -(n+1:ℤ) ∨ 0<p → IsZero (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)
  (hbr : ∑ k∈Finset.range (n+2),(-1:ℝ)^k*(b (-(n+1:ℤ)+k):ℝ)=0)

omit [Nontrivial R] in
include hgen hds hmu ha B hf hb hbr in
lemma quotient_root_euler (r : Fin n → ℤ) :
    (-1:ℝ)^(n+1)*finiteHomologyEuler ell
      ((quotientAt I z hz F (n+1) s hd (rootAmbient s r 0)).total (.up ℤ))
        (-(n+1:ℤ)) ((n+1)+(n+1))=
      -(ell.realValue (ModuleCat.of R (R ⧸ I)))*
        ∑ i∈Finset.range (n+2),(-1:ℝ)^i*(b (-(i:ℤ)):ℝ)*rootStripPolynomial n r i s := by
  have hflat : ∀ p,Module.Flat R (F.X p) := fun p => by have := hf p; infer_instance
  have he := quotientAtTotal_euler I z hz F (n+1) s hd (rootAmbient s r 0)
    hb hgen ell hds hmu ha b B hflat ((n+1)+(n+1)) (by omega)
  simp only [Nat.cast_add,Nat.cast_one] at he
  have hrw : (∑ k∈Finset.range (n+1+1),(-1:ℝ)^k*(b (-(n+1:ℤ)+k):ℝ)*
      ∑ j∈Finset.range (IdealFiltered.order (n+1) s (-(n+1:ℤ)+k)),
        finiteHomologyEuler ell (exceptionalZ I z hz (raise (rootAmbient s r 0) j)) 0 n)=
      ell.realValue (ModuleCat.of R (R ⧸ I))*
        ∑ k∈Finset.range (n+2),(-1:ℝ)^k*(b (-(n+1:ℤ)+k):ℝ)*rootPrefix n r (n+1) s (k*s) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have ho : IdealFiltered.order (n+1) s (-(n+1:ℤ)+k)=k*s := by
      unfold IdealFiltered.order
      congr 1
      omega
    rw [ho,ambientStrip_euler I z hz hgen ell hds hmu ha]
    ring
  rw [he,hrw]
  calc
    _=ell.realValue (ModuleCat.of R (R ⧸ I))*
        ((-1:ℝ)^(n+1)*(∑ k∈Finset.range (n+2),(-1:ℝ)^k*(b (-(n+1:ℤ)+k):ℝ)*
          rootPrefix n r (n+1) s (k*s))) := by ring
    _=_ := by
      have hc := complement_euler n r (n+1) s (fun p => (b p:ℝ)) hbr
      simp only [Nat.cast_add,Nat.cast_one] at hc
      rw [hc]
      ring

include hz hgen hds hmu ha hK hd B hf hfin hb hac hbr in
 

theorem sum_estimate_oai (r : Fin n → ℤ) (hr : RootPositions n s r) :
    0≤(n.factorial:ℝ)*ell.realValue (F.homology 0)+
      ell.realValue (ModuleCat.of R (R ⧸ I))*
        ∑ i∈Finset.range (n+2),(-1:ℝ)^i*(b (-(i:ℤ)):ℝ)*rootStripPolynomial n r i s := by
  have hflat : ∀ p,Module.Flat R (F.X p) := fun p => by have := hf p; infer_instance
  have hp : ∀ p,Module.Projective R (F.X p) := fun p => by have := hf p; infer_instance
  have hpos := (rootTotal_euler_nonnegative I z hz hgen ell hds hmu ha F s hd b B hflat hp hfin hb hac
    r hr ((n+1)+(n+1)) (by omega)).2.2
  have he := ambient_euler_additive I z hz F (n+1) s hd (rootAmbient s r 0)
    hb hgen ell hds hmu ha b B hflat hp hfin hac ((n+1)+(n+1)) (by omega)
  have hu : (-1:ℝ)^(n+1)*finiteHomologyEuler ell
      ((unfilteredAt I z hz F (rootAmbient s r 0)).total (.up ℤ))
        (-(n+1:ℤ)) ((n+1)+(n+1))=(n.factorial:ℝ)*ell.realValue (F.homology 0) := by
    rw [←(show tensorCech F (cechDiagram I z hz (rootAmbient s r 0))=
      (unfilteredAt I z hz F (rootAmbient s r 0)).total (.up ℤ) from rfl)]
    have huv := unfilteredEuler_rank I z hz ell F (n+1) hgen hds hmu ha b B hflat hp hfin hb hac hbr
      (rootAmbient s r 0)
    rw [scalarEuler_value I z hz F hgen ell hds hmu ha hK hf hfin hb hac] at huv
    simpa only [unfilteredEuler,tensorEuler,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using huv
  have hq := quotient_root_euler I z hz hgen ell hds hmu ha F s hd b B hf hb hbr r
  simp only [Nat.cast_add,Nat.cast_one] at he
  have hh := congrArg (fun x : ℝ => (-1:ℝ)^(n+1)*x) he
  rw [mul_add,hu,hq] at hh
  linarith only [hh,hpos]
end Lech.ReesRoot

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.ReesRoot.sum_estimate_oai.{u} := @OAI.Lech.ReesRoot.sum_estimate_oai.{u}
